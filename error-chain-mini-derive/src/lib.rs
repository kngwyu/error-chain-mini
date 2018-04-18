extern crate proc_macro;
extern crate syn;
#[macro_use]
extern crate synstructure;
#[macro_use]
extern crate quote;

decl_derive!([ErrorKind, attributes(msg)] => error_kind_derive);

fn error_kind_derive(s: synstructure::Structure) -> quote::Tokens {
    let short_body = s.each_variant(|v| {
        let msg = find_msg(&v.ast().attrs).expect("All variants must have msg attiribute.");
        let metas = msg.nested;
        if metas.is_empty() {
            panic!("You have to implement `#[msg(short = \"your description\")]`");
        }
        let mut res = None;
        for meta in metas.iter() {
            if let Some(tokens) = process_short(meta) {
                if res.is_some() {
                    panic!("Cannot have multiple `short = ` attributes")
                }
                res = Some(tokens);
            }
        }
        if let Some(tokens) = res {
            tokens
        } else {
            panic!("You have to implement `short = ..` attribute")
        }
    });
    s.bound_impl(
        quote!(::error_chain_mini::ErrorKind),
        quote! {
            fn short(&self) -> &str {
                match *self { #short_body }
            }
        },
    )
}

fn process_short(nested: &syn::NestedMeta) -> Option<quote::Tokens> {
    let res = match nested {
        syn::NestedMeta::Meta(syn::Meta::NameValue(nameval)) => {
            if nameval.ident == "detailed" {
                return None;
            }
            if nameval.ident != "short" {
                panic!("only short=.. or detailed.. is allowed");
            }
            if let syn::Lit::Str(ref lit_str) = nameval.lit {
                let val = lit_str.value();
                quote!(#val)
            } else {
                panic!("Oly string literal is allowed.")
            }
        }
        syn::NestedMeta::Literal(lit) => {
            if let syn::Lit::Str(lit_str) = lit {
                let val = lit_str.value();
                quote!(#val)
            } else {
                panic!("Oly string literal is allowed.")
            }
        }
        _ => panic!("you have to write like #[msg(\"your description\")]"),
    };
    Some(res)
}

fn find_msg(attrs: &[syn::Attribute]) -> Option<syn::MetaList> {
    let mut res = None;
    for attr in attrs {
        let meta = attr.interpret_meta();
        if let Some(syn::Meta::List(list)) = meta {
            if list.ident == "msg" {
                if res.is_some() {
                    panic!("Cannot have multiple `cause` attributes");
                }
                res = Some(list);
            }
        }
    }
    res
}

// #[cfg(test)]
// mod codegen_test {
//     use super::*;
//     #[test]
//     fn short_only_enum() {
//         test_derive! {
//             error_kind_derive {
//                 enum MyError {
//                     #[msg(short = "error kind 1")]
//                     Kind1,
//                     #[msg(short = "error kind 2")]
//                     Kind2
//                 }
//             }
//             expands to {
//                 const A: usize = 4;
//             }
//         }
//     }
// }
