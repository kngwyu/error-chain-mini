//! derive for

extern crate proc_macro;
extern crate syn;
#[macro_use]
extern crate synstructure;
#[macro_use]
extern crate quote;

decl_derive!([ErrorKind, attributes(msg)] => error_kind_derive);

fn error_kind_derive(s: synstructure::Structure) -> quote::Tokens {
    let short_body = s.each_variant(|v| {
        if let Some(msg) = find_msg(&v.ast().attrs) {
            let metas = msg.nested;
            if metas.is_empty() {
                panic!("You have to implement `#[msg(short = \"your description\")]`");
            }
            let mut filterd = metas.iter().filter_map(process_short);
            if let Some(tokens) = filterd.next() {
                if filterd.next().is_some() {
                    panic!("Cannot implment short=.. multiple times");
                }
                tokens
            } else {
                panic!("You have to implement `short = ..` attribute")
            }
        } else {
            let par_name = s.ast().ident.as_ref();
            let variant_name = v.ast().ident.as_ref();
            if par_name != variant_name {
                quote!(concat!(#par_name, "::", #variant_name))
            } else {
                quote!(#par_name)
            }
        }
    });
    let mut has_detailed = false;
    let detailed_body = s.each_variant(|v| {
        if let Some(t) = process_detailed(v) {
            has_detailed = true;
            t
        } else {
            quote!(String::new())
        }
    });
    let mut res = s.bound_impl(
        quote!(::error_chain_mini::ErrorKind),
        quote! {
            fn short(&self) -> &str {
                match *self { #short_body }
            }
            fn detailed(&self) -> String {
                match *self { #detailed_body }
            }
        },
    );
    let display_body = if has_detailed {
        quote!(write!(f, "{} {{ {} }}", self.short(), self.detailed()))
    } else {
        quote!(write!(f, "{}", self.short()))
    };
    let display = s.bound_impl(
        quote!(::std::fmt::Display),
        quote! {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                #display_body
            }
        },
    );
    res.append_all(display);
    res
}

fn process_detailed(variant: &synstructure::VariantInfo) -> Option<quote::Tokens> {
    let msg = find_msg(&variant.ast().attrs)?;
    let nested = msg.nested;
    let mut iter = nested.iter().skip_while(|nested| match nested {
        syn::NestedMeta::Meta(syn::Meta::NameValue(nameval)) => nameval.ident != "detailed",
        _ => panic!("Invlaid Value"),
    });
    let detailed = iter.next()?;
    let s = if let syn::NestedMeta::Meta(syn::Meta::NameValue(nameval)) = detailed {
        if let syn::Lit::Str(ref lit) = nameval.lit {
            lit.value()
        } else {
            panic!("Only string is allowed after detailed=")
        }
    } else {
        unreachable!();
    };
    macro_rules! get_nth {
        ($id: expr) => {{
            let bi = variant.bindings().into_iter().nth($id);
            if let Some(bi) = bi {
                bi.binding
            } else {
                panic!("Invalid index {} for {:?}", $id, variant.prefix);
            }
        }};
    }
    let args = iter.take_while(|arg| {
        if let syn::NestedMeta::Meta(syn::Meta::NameValue(_)) = arg {
            false
        } else {
            true
        }
    }).map(|arg| match arg {
        syn::NestedMeta::Literal(syn::Lit::Int(int)) => {
            let idx = int.value() as usize;
            let bi = get_nth!(idx);
            quote!(#bi)
        }
        syn::NestedMeta::Meta(syn::Meta::Word(ident)) => {
            if ident.as_ref().starts_with("_") {
                if let Ok(idx) = ident.as_ref()[1..].parse::<usize>() {
                    let bi = get_nth!(idx);
                    return quote!(#bi);
                }
            }
            if let Some(bi) = variant
                .bindings()
                .into_iter()
                .find(|bi| bi.ast().ident.as_ref() == Some(ident))
            {
                let bi = bi.binding;
                quote!(#bi)
            } else {
                panic!(
                    "Invalid argument {} for {:?}",
                    ident.as_ref(),
                    variant.prefix
                );
            }
        }
        _ => panic!("Invalid argument to detailed=.."),
    });
    Some(quote!(format!(#s #(, #args)*)))
}

fn process_short(nested: &syn::NestedMeta) -> Option<quote::Tokens> {
    match nested {
        syn::NestedMeta::Meta(syn::Meta::NameValue(nameval)) => {
            if nameval.ident == "detailed" {
                return None;
            }
            if nameval.ident != "short" {
                panic!("only short=.. or detailed=.. is allowed");
            }
            if let syn::Lit::Str(ref lit_str) = nameval.lit {
                let val = lit_str.value();
                Some(quote!(#val))
            } else {
                panic!("Oly string literal is allowed after short")
            }
        }
        _ => None,
    }
}

fn find_msg(attrs: &[syn::Attribute]) -> Option<syn::MetaList> {
    let mut res = None;
    for attr in attrs {
        let meta = attr.interpret_meta();
        if let Some(syn::Meta::List(list)) = meta {
            if list.ident == "msg" {
                if res.is_some() {
                    panic!("Cannot have multiple `msg` attributes");
                }
                res = Some(list);
            }
        }
    }
    res
}
