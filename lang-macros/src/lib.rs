use proc_macro2::TokenStream;
use quote::{format_ident,quote};
use syn::{Attribute,Data,DeriveInput,Field,Fields,Ident,Lit,Meta,NestedMeta,Type,Variant,parse_macro_input};

enum TypeOfThing {
    Symbol(String),
    Keyword(String),
    Structure,
}

enum TypeOfVariant {
    Symbol(String),
    Keyword(String),
    Concat(Vec<Type>),
}

struct ToDerive {
    parse: bool,
    display: bool,
}

#[proc_macro_derive(Parse, attributes(symbol, keyword))]
pub fn derive_parse(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive_things(input, ToDerive{parse:true, display:true})
}

#[proc_macro_derive(ParseDisplay, attributes(symbol, keyword))]
pub fn derive_display(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive_things(input, ToDerive{parse:false, display:true})
}

fn derive_things(input: proc_macro::TokenStream, to_derive: ToDerive) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let (parse_body, display_body) = match parse_attribs(&input.attrs) {
        TypeOfThing::Symbol(sym) => {
            if !is_span_struct(&input) {
                panic!("#[symbol] can only be attached to a struct with a single unnamed Span param");
            }
            (gen_sym(name, &sym), gen_sym_display(&sym))
        }
        TypeOfThing::Keyword(keyword) => {
            if !is_span_struct(&input) {
                panic!("#[keyword] can only be attached to a struct with a single unnamed Span param");
            }
            (gen_keyword(name, &keyword), gen_keyword_display(&keyword))
        }
        TypeOfThing::Structure => {
            if let Some(fields) = is_named_struct(&input) {
                (gen_struct(name, &fields), gen_struct_display(&fields))
            } else if let Some(variants) = is_enum(&input) {
                (gen_enum(name, &variants), gen_enum_display(&variants))
            } else {
                panic!("Structure must have named fields");
            }
        }
    };

    gen_impls(name, parse_body, display_body, to_derive).into()
}

/////////////////
//
// Display
//
/////////////////

fn gen_struct_display(fields: &[Field]) -> TokenStream {
    let lines:Vec<_> = fields.iter().map(gen_struct_display_line).collect();
    quote! {
        #(#lines)*
        Ok(())
    }
}

fn gen_struct_display_line(f: &Field) -> TokenStream {
    let name = &f.ident;
    write(&f.ty, quote!{&self.#name})
}

fn write(ty: &Type, name: TokenStream) -> TokenStream {
    if let Type::Path(p) = ty {
        let segs = &p.path.segments;
        if segs.len() == 1 && &segs[0].ident.to_string() == "Option" {
            // Can't implement Display on Option<T>, so we have to special-case it.
            return quote! {
                if let Some(x) = #name {
                    write!(f, "{}", x)?;
                }
            }
        } else if segs.len() == 1 && &segs[0].ident.to_string() == "Vec" {
            // Similarly with Vec
            return quote! {
                for x in #name {
                    write!(f, "{}", x)?;
                }
            }
        }
    }
    quote! {
        write!(f, "{}", #name)?;
    }
}

fn gen_enum_display(variants: &[Variant]) -> TokenStream {
    let lines:Vec<_> = variants.iter().map(gen_enum_display_line).collect();
    quote! {
        match self {
            #(#lines)*
        }
    }
}

fn gen_enum_display_line(variant: &Variant) -> TokenStream {
    let name = &variant.ident;
    match get_type_of_variant(variant) {
        TypeOfVariant::Symbol(sym) => quote! {
            Self::#name(_) => write!(f, "{}", #sym),
        },
        TypeOfVariant::Keyword(keyword) => quote! {
            Self::#name(_) => write!(f, "{} ", #keyword),
        },
        TypeOfVariant::Concat(ts) => {
            let xs:Vec<_> = (0..ts.len()).map(|i|format_ident!("x{}",i)).collect();
            let lines:Vec<_> = (0..ts.len()).map(|i|{
                let x = &xs[i];
                write(&ts[i],quote!{#x})
            }).collect();
            quote! {
                Self::#name(#(#xs,)*) => {
                    #(#lines)*
                    Ok(())
                }
            }
        },
    }
}

fn gen_sym_display(sym: &str) -> TokenStream {
    quote! {
        write!(f, "{}", #sym)
    }
}

fn gen_keyword_display(keyword: &str) -> TokenStream {
    quote! {
        write!(f, "{} ", #keyword)
    }
}

///////////////////
//
// Parse
//
///////////////////

fn gen_struct(name: &Ident, fields: &[Field]) -> TokenStream {
    let lines:Vec<_> = fields.iter().map(gen_struct_line).collect();
    let field_names:Vec<_> = fields.iter().map(|f| f.ident.clone()).collect();
    quote! {
        #(#lines)*
        Ok((input, #name {
            #(#field_names,)*
        }))
    }
}

fn gen_struct_line(f: &Field) -> TokenStream {
    let name = &f.ident;
    let ty = &f.ty;
    quote! {
        let (input,#name) = <#ty>::parse(input)?;
    }
}

fn gen_enum(_name: &Ident, variants: &[Variant]) -> TokenStream {
    let lines:Vec<_> = variants.iter().map(gen_enum_line).collect();
    if lines.len() == 1 {
        let line = &lines[0];
        quote! {
            #line(input)
        }
    } else {
        quote! {
            nom::branch::alt((
                #(#lines,)*
            ))(input)
        }
    }
}

fn gen_enum_line(variant: &Variant) -> TokenStream {
    let name = &variant.ident;
    match get_type_of_variant(variant) {
        TypeOfVariant::Symbol(sym) => quote! {
            nom::combinator::map(lang_stuff::spanned_symbol(#sym), Self::#name)
        },
        TypeOfVariant::Keyword(keyword) => quote! {
            nom::combinator::map(lang_stuff::spanned_keyword(#keyword), Self::#name)
        },
        TypeOfVariant::Concat(ts) => {
            let xs:Vec<_> = (0..ts.len()).map(|i|format_ident!("x{}",i)).collect();
            quote! {
                nom::combinator::map(nom::sequence::tuple((#(<#ts>::parse,)*)), |(#(#xs,)*)|Self::#name(#(#xs,)*))
            }
        },
    }
}

fn gen_sym(name: &Ident, sym: &str) -> TokenStream {
    quote! {
        let (input,sym) = lang_stuff::spanned_symbol(#sym)(input)?;
        Ok((input,#name(sym)))
    }
}

fn gen_keyword(name: &Ident, keyword: &str) -> TokenStream {
    quote! {
        let (input,sym) = lang_stuff::spanned_keyword(#keyword)(input)?;
        Ok((input,#name(sym)))
    }
}

fn gen_impls(name: &Ident, parse_body: TokenStream, display_body: TokenStream, to_derive: ToDerive) -> TokenStream {
    let parse = if to_derive.parse {
        quote! {
            impl lang_stuff::Parse for #name {
                fn parse(input: &str) -> nom::IResult<&str, Self, lang_stuff::Error> {
                    #parse_body
                }
            }
        }
    } else {
        quote!{}
    };

    let display = if to_derive.display {
        quote! {
            impl std::fmt::Display for #name {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    #display_body
                }
            }
        }
    } else {
        quote!{}
    };

    quote!{ #parse #display }
}

/////////////
//
// Other stuff
//
/////////////

fn is_named_struct(input: &DeriveInput) -> Option<Vec<Field>> {
    if let Data::Struct(ds) = &input.data {
        if let Fields::Named(fields) = &ds.fields {
            return Some(fields.named.clone().into_iter().collect())
        }
    }
    None
}

fn is_span_struct(input: &DeriveInput) -> bool {
    if let Data::Struct(ds) = &input.data {
        if let Fields::Unnamed(un) = &ds.fields {
            return un.unnamed.len() == 1;   // TODO: check type as well?
        }
    }
    false
}

fn is_span_variant(variant: &Variant) -> bool {
    if let Fields::Unnamed(un) = &variant.fields {
        return un.unnamed.len() == 1;    // TODO: check type as well?
    }
    false
}

fn is_unnamed_arg_variant(variant: &Variant) -> Option<Vec<Type>> {
    if let Fields::Unnamed(un) = &variant.fields {
        return Some(un.unnamed.iter().map(|u|u.ty.clone()).collect())
    }
    None
}

fn is_enum(input: &DeriveInput) -> Option<Vec<Variant>> {
    if let Data::Enum(en) = &input.data {
        return Some(en.variants.clone().into_iter().collect())
    }
    None
}

fn is_one_string_param(attr: &Attribute) -> Option<String> {
    if let Meta::List(meta) = attr.parse_meta().unwrap() {
        if meta.nested.len() == 1 {
            if let Some(NestedMeta::Lit(Lit::Str(lit))) = meta.nested.first() {
                return Some(lit.value())
            }
        }
    }
    None
}

fn parse_attribs(attrs: &[Attribute]) -> TypeOfThing {
    let mut symbol = None;
    let mut keyword = None;
    let mut count = 0;
    for attr in attrs {
        if attr.path.is_ident("symbol") {
            symbol = Some(is_one_string_param(attr).expect("symbol should have one string param"));
            count += 1;
        }
        if attr.path.is_ident("keyword") {
            keyword = Some(is_one_string_param(attr).expect("keyword should have one string param"));
            count += 1;
        }
    }

    match count {
        0 => TypeOfThing::Structure,
        1 => {
            if let Some(sym) = symbol {
                TypeOfThing::Symbol(sym)
            } else if let Some(keyword) = keyword {
                TypeOfThing::Keyword(keyword)
            } else {
                unreachable!()
            }
        }
        _ => panic!("Expected at most one of #[symbol], #[keyword]")
    }
}

fn get_type_of_variant(variant: &Variant) -> TypeOfVariant {
    match parse_attribs(&variant.attrs) {
        TypeOfThing::Symbol(keyword) =>
            if is_span_variant(variant) {
                TypeOfVariant::Symbol(keyword)
            } else {
                panic!("Enum variant {} must have a single Span param", variant.ident);
            }
        TypeOfThing::Keyword(keyword) =>
            if is_span_variant(variant) {
                TypeOfVariant::Keyword(keyword)
            } else {
                panic!("Enum variant {} must have a single Span param", variant.ident);
            }
        TypeOfThing::Structure =>
            if let Some(ts) = is_unnamed_arg_variant(variant) {
                TypeOfVariant::Concat(ts)
            } else {
                panic!("Enum variant {} must have a single param", variant.ident);
            }
    }
}
