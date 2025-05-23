#![allow(unused_imports)]
use super::super::prelude::*;

use core::option::Option;
use core::option::Option::None;
use core::option::Option::Some;

verus! {

////// Add is_variant-style spec functions
pub trait OptionAdditionalFns<T>: Sized {
    #[allow(non_snake_case)]
    spec fn is_Some(&self) -> bool;

    #[allow(non_snake_case)]
    spec fn get_Some_0(&self) -> T;

    #[allow(non_snake_case)]
    spec fn is_None(&self) -> bool;

    #[allow(non_snake_case)]
    spec fn arrow_Some_0(&self) -> T;

    #[allow(non_snake_case)]
    spec fn arrow_0(&self) -> T;

    proof fn tracked_unwrap(tracked self) -> (tracked t: T)
        requires
            self.is_Some(),
        ensures
            t == self.get_Some_0(),
    ;

    proof fn tracked_borrow(tracked &self) -> (tracked t: &T)
        requires
            self.is_Some(),
        ensures
            t == self.get_Some_0(),
    ;
}

impl<T> OptionAdditionalFns<T> for Option<T> {
    #[verifier::inline]
    open spec fn is_Some(&self) -> bool {
        is_variant(self, "Some")
    }

    #[verifier::inline]
    open spec fn get_Some_0(&self) -> T {
        get_variant_field(self, "Some", "0")
    }

    #[verifier::inline]
    open spec fn is_None(&self) -> bool {
        is_variant(self, "None")
    }

    #[verifier::inline]
    open spec fn arrow_Some_0(&self) -> T {
        get_variant_field(self, "Some", "0")
    }

    #[verifier::inline]
    open spec fn arrow_0(&self) -> T {
        get_variant_field(self, "Some", "0")
    }

    proof fn tracked_unwrap(tracked self) -> (tracked t: T) {
        match self {
            Option::Some(t) => t,
            Option::None => proof_from_false(),
        }
    }

    proof fn tracked_borrow(tracked &self) -> (tracked t: &T) {
        match self {
            Option::Some(t) => t,
            Option::None => proof_from_false(),
        }
    }
}

////// Specs for std methods
// is_some
#[verifier::inline]
pub open spec fn is_some<T>(option: &Option<T>) -> bool {
    is_variant(option, "Some")
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(is_some)]
pub fn ex_option_is_some<T>(option: &Option<T>) -> (b: bool)
    ensures
        b == is_some(option),
{
    option.is_some()
}

// is_none
#[verifier::inline]
pub open spec fn is_none<T>(option: &Option<T>) -> bool {
    is_variant(option, "None")
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(is_none)]
pub fn ex_option_is_none<T>(option: &Option<T>) -> (b: bool)
    ensures
        b == is_none(option),
{
    option.is_none()
}

// as_ref
#[verifier::external_fn_specification]
pub fn as_ref<T>(option: &Option<T>) -> (a: Option<&T>)
    ensures
        a.is_Some() <==> option.is_Some(),
        a.is_Some() ==> option.get_Some_0() == a.get_Some_0(),
{
    option.as_ref()
}

// unwrap
#[verifier::inline]
pub open spec fn spec_unwrap<T>(option: Option<T>) -> T
    recommends
        option.is_Some(),
{
    option.get_Some_0()
}

#[verifier::when_used_as_spec(spec_unwrap)]
#[verifier::external_fn_specification]
pub fn unwrap<T>(option: Option<T>) -> (t: T)
    requires
        option.is_Some(),
    ensures
        t == spec_unwrap(option),
{
    option.unwrap()
}

// unwrap_or
#[verifier::inline]
pub open spec fn spec_unwrap_or<T>(option: Option<T>, default: T) -> T {
    match option {
        Some(t) => t,
        None => default,
    }
}

#[verifier::when_used_as_spec(spec_unwrap_or)]
#[verifier::external_fn_specification]
pub fn unwrap_or<T>(option: Option<T>, default: T) -> (t: T)
    ensures
        t == spec_unwrap_or(option, default),
{
    option.unwrap_or(default)
}

#[verifier::external_fn_specification]
pub fn take<T>(option: &mut Option<T>) -> (t: Option<T>)
    ensures
        t == old(option),
        *option is None,
{
    option.take()
}

#[verifier::external_fn_specification]
pub fn ex_map<T, U, F: FnOnce(T) -> U>(a: Option<T>, f: F) -> (ret: Option<U>)
    requires
        a.is_some() ==> f.requires((a.unwrap(),)),
    ensures
        ret.is_some() == a.is_some(),
        ret.is_some() ==> f.ensures((a.unwrap(),), ret.unwrap()),
{
    a.map(f)
}

#[verifier::external_fn_specification]
pub fn ex_option_clone<T: Clone>(opt: &Option<T>) -> (res: Option<T>)
    ensures
        opt.is_none() ==> res.is_none(),
        opt.is_some() ==> res.is_some() && call_ensures(T::clone, (&opt.unwrap(),), res.unwrap()),
{
    opt.clone()
}

// ok_or
#[verifier::inline]
pub open spec fn spec_ok_or<T, E>(option: Option<T>, err: E) -> Result<T, E> {
    match option {
        Some(t) => Ok(t),
        None => Err(err),
    }
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(spec_ok_or)]
pub fn ex_ok_or<T, E>(option: Option<T>, err: E) -> (res: Result<T, E>)
    ensures
        res == spec_ok_or(option, err),
{
    option.ok_or(err)
}

} // verus!
