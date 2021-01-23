use proc_macro2::TokenStream;
use quote::quote;
use syn::{Attribute,Data,DeriveInput,Field,Fields,Ident,Lit,Meta,NestedMeta,parse_macro_input};

enum TypeOfThing {
    Symbol(String),
    Keyword(String),
    Structure,
}

#[proc_macro_derive(Parse, attributes(symbol, keyword))]
pub fn derive_parse(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let parse_body = match parse_attribs(&input.attrs) {
        TypeOfThing::Symbol(sym) => {
            if !is_span_struct(&input) {
                panic!("#[symbol] can only be attached to a struct with a single unnamed Span param");
            }
            gen_sym(name, &sym)
        }
        TypeOfThing::Keyword(keyword) => {
            if !is_span_struct(&input) {
                panic!("#[keyword] can only be attached to a struct with a single unnamed Span param");
            }
            gen_keyword(name, &keyword)
        }
        TypeOfThing::Structure => {
            if let Some(fields) = is_named_struct(&input) {
                gen_struct(name, &fields)
            } else {
                panic!("Structure must have named fields");
            }
        }
    };

    gen_impl(name, parse_body).into()
}

fn gen_struct(name: &Ident, fields: &[Field]) -> TokenStream {
    let lines:Vec<_> = fields.iter().map(gen_struct_line).collect();
    let field_names:Vec<_> = fields.iter().map(|f| f.ident.clone()).collect();

    quote! {
        #(#lines)*
        Ok(input, #name {
            #(#field_names,)*
        })
    }
}

fn gen_struct_line(f: &Field) -> TokenStream {
    let name = &f.ident;
    let ty = &f.ty;
    quote! {
        let (input,#name) = #ty::parse(input)?;
    }
}

fn gen_sym(name: &Ident, sym: &str) -> TokenStream {
    quote! {
        let (input,sym) = lang_stuff::spanned_symbol(input, #sym)?;
        Ok((input,#name(sym)))
    }
}

fn gen_keyword(name: &Ident, keyword: &str) -> TokenStream {
    quote! {
        let (input,sym) = lang_stuff::spanned_keyword(input, #keyword)?;
        Ok((input,#name(sym)))
    }
}

fn gen_impl(name: &Ident, parse_body: TokenStream) -> TokenStream {
    quote! {
        impl lang_stuff::Parse for #name {
            fn parse(input: &str) -> nom::IResult<&str, Self, lang_stuff::Error> {
                #parse_body
            }
        }
    }
}

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
