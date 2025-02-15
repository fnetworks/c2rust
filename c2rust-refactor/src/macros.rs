#[macro_export]
macro_rules! match_or {
    ([$e:expr] $($arm_pat:pat => $arm_body:expr),*; $or:expr) => {
        match $e {
            $( $arm_pat => $arm_body, )*
            _ => $or,
        }
    };
}

#[macro_export]
macro_rules! expect {
    ([$e:expr] $arm_pat:pat => $arm_body:expr) => {
        match_or!([$e] $arm_pat => $arm_body;
            panic!(concat!("expected ", stringify!($arm_pat))))
    };
    ([$e:expr] $($arm_pat:pat => $arm_body:expr),*) => {
        match_or!([$e] $($arm_pat => $arm_body),*;
            panic!(concat!("expected one of: ",
                           stringify!($($arm_pat),*))))
    };
}

#[macro_export]
macro_rules! unpack {
    ([$e:expr] $enum_:ident :: $variant:ident ( $($arg:ident),* )) => {
        let ($($arg,)*) = expect!([$e] $enum_::$variant($($arg),*) => ($($arg,)*));
    };
}

// TODO deprecated - collides with rust's std::cmatches!(..)
#[macro_export]
macro_rules! matches {
    ([$e:expr] $($pat:pat),*) => {
        match $e {
            $( $pat => true, )*
            _ => false,
        }
    };
}

#[macro_export]
macro_rules! cmatches {
    ([$e:expr] $($pat:pat),*) => {
        match $e {
            $( $pat => true, )*
            _ => false,
        }
    };
}

#[macro_export]
#[cfg(feature = "profile")]
macro_rules! profile_start {
    ($msg:expr) => {
        flame::start($msg)
    }
}

#[macro_export]
#[cfg(not(feature = "profile"))]
macro_rules! profile_start {
    ($msg:expr) => {}
}

#[macro_export]
#[cfg(feature = "profile")]
macro_rules! profile_end {
    ($msg:expr) => {
        flame::end($msg)
    }
}

#[macro_export]
#[cfg(not(feature = "profile"))]
macro_rules! profile_end {
    ($msg:expr) => {}
}
