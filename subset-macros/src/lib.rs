use proc_macro2::TokenStream;
use quote::{format_ident,quote};
use syn::{Data,DataEnum,DataStruct,DeriveInput,parse_macro_input};

#[proc_macro_derive(PaLift)]
pub fn derive_palift(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let variants;
    let extra;
    match &input.data {
        Data::Struct(structure) => {
            variants = vec![(name.clone(), structure.fields.clone())];
            extra = derive_palift_struct(structure);
        }
        Data::Enum(enumeration) => {
            variants = enumeration.variants.iter().map(|variant|(variant.ident.clone(), variant.fields.clone())).collect();
            extra = derive_palift_enum(enumeration);
        }
        _ => panic!("Cannot handle untagged union")
    };

    let pa_variants = variants.iter().map(|(vname, vfields)| {
        let vname_str = vname.to_string();
        let pa_fields = vfields.iter().map(|vfield| {
            let ty = &vfield.ty;
            quote! {<#ty>::pa_type()}
        }).collect::<Vec<_>>();
        quote!{
            subset_stuff::PaVariant(#vname_str.to_owned(), vec![#(#pa_fields,)*])
        }
    }).collect::<Vec<_>>();

    (quote! {
        impl subset_stuff::PaLift for #name {
            fn pa_type() -> subset_stuff::PaType {
                subset_stuff::PaType::Enum(vec![
                    #(#pa_variants,)*
                ])
            }
            #extra
        }

    }).into()
}

fn derive_palift_struct(structure: &DataStruct) -> TokenStream {
    let pa_fields = structure.fields.iter().map(|field| {
        let name = &field.ident;
        quote!{self.#name.pa_lift()}
    }).collect::<Vec<_>>();
    quote! {
        fn pa_lift(&self) -> subset_stuff::PaValue {
            subset_stuff::PaValue::Variant(Self::pa_type(), 0, vec![#(#pa_fields,)*])
        }
    }
}

fn derive_palift_enum(enumeration: &DataEnum) -> TokenStream {
    let branches = enumeration.variants.iter().enumerate().map(|(i,variant)| {
        let name = &variant.ident;
        let fields = (0..variant.fields.len()).map(|j|format_ident!("f{}",j)).collect::<Vec<_>>();
        quote!{
            Self::#name(#(#fields,)*) => subset_stuff::PaValue::Variant(Self::pa_type(),#i,vec![#(#fields.pa_lift(),)*]),
        }
    }).collect::<Vec<_>>();
    quote! {
        fn pa_lift(&self) -> subset_stuff::PaValue {
            match self {
                #(#branches)*
            }
        }
    }
}
