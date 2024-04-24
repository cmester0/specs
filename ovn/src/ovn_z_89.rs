#![no_std]
#![feature(register_tool)]
#![register_tool(hax)]

#[hax_lib_macros::exclude]
extern crate hax_lib_macros;

#[hax_lib_macros::exclude]
use hax_lib_macros::*;

#[exclude]
use hacspec_concordium::*;
#[exclude]
use hacspec_concordium_derive::*;

pub use crate::ovn_traits::*;

// // pub use create::ovn_traits::*;
// use create::Field;
// use create::Group;
// use create::Field;

////////////////////
// Impl for Z/89Z //
////////////////////

#[derive(Clone, Copy, PartialEq, Eq, hacspec_concordium::Serial, hacspec_concordium::Deserial)]
pub struct z_89 { val : u8 }

// impl hacspec_concordium::Deserial for z_89 {
//     // TODO:
//     fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
//         let v : u8 = source.get()?;
//         Ok(z_89 {
//             val: v,
//         })
//     }
// }

// impl hacspec_concordium::Serial for z_89 {
//     // TODO:
//     fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
//         self.val.serial(out)
//     }
// }

impl Field for z_89 {
    fn q() -> Self {
        z_89{ val: 89u8}
    } // Prime order
    fn random_field_elem(random: u32) -> Self {
        z_89{ val: random as u8 % (Self::q().val - 1) }
    }

    fn field_zero() -> Self {
        z_89{ val: 0u8 }
    }

    fn field_one() -> Self {
        z_89{ val: 1u8 }
    }

    fn add(x: Self, y: Self) -> Self {
        z_89{ val: (x.val + y.val) % (Self::q().val - 1) }
    }

    fn sub(x: Self, y: Self) -> Self {
        z_89{ val: (x.val + (Self::q().val - 1) - y.val) % (Self::q().val - 1) }
    }

    fn mul(x: Self, y: Self) -> Self {
        z_89{ val: (((x.val as u16) * (y.val as u16)) % ((Self::q().val - 1) as u16)) as u8 }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, hacspec_concordium::Serial, hacspec_concordium::Deserial)]
pub struct g_z_89 { val : u8 }

// impl hacspec_concordium::Deserial for g_z_89 {
//     // TODO:
//     fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
//         let v : u8 = source.get()?;

//         Ok(g_z_89 {
//             val: v,
//         })
//     }
// }

// impl hacspec_concordium::Serial for g_z_89 {
//     // TODO:
//     fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
//         self.val.serial(out)
//     }
// }


impl Group for g_z_89 {
    type Z = z_89;
    
    fn g() -> Self {
        g_z_89 { val: 3u8 }
    } // Generator (elemnent of group)

    fn hash(x: Vec<Self>) -> z_89 {
        let mut res = z_89::field_one();
        for y in x {
            res = z_89::mul(z_89{val: y.val}, res);
        }
        res // TODO
    }

    fn g_pow(x: z_89) -> Self {
        Self::pow(Self::g(), x)
    }

    // TODO: use repeated squaring instead!
    fn pow(g: Self, x: z_89) -> Self {
        let mut result = Self::group_one();
        for _ in 0..(x.val % (z_89::q().val - 1)) {
            result = Self::prod(result, g);
        }
        result
    }

    fn group_one() -> Self {
        g_z_89 { val: 1 }
    }

    fn prod(x: Self, y: Self) -> Self {
        let q_val = z_89::q().val;
        g_z_89 { val: ((((x.val % q_val) as u16) * ((y.val % q_val) as u16)) % (q_val as u16)) as u8 }
    }

    fn inv(x: Self) -> Self {
        for j in 0..89 {
            let value = g_z_89 {val: j};
            if Self::prod(x, value) == Self::group_one() {
                return value;
            }
        }
        assert!(false);
        return x;
    }

    fn div(x: Self, y: Self) -> Self {
        Self::prod(x, Self::inv(y))
    }
}
