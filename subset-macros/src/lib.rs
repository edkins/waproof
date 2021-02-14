use quote::quote;
use syn::{Data,DeriveInput,parse_macro_input};

#[proc_macro_derive(PaLift)]
pub fn derive_paify(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let variants = match &input.data {
        Data::Struct(structure) => {
            vec![(name.clone(), structure.fields.clone())]
        }
        Data::Enum(enumeration) => {
            enumeration.variants.iter().map(|variant|(variant.ident.clone(), variant.fields.clone())).collect()
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
        }

    }).into()
}
