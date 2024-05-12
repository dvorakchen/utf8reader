//! Read UTF-8 characters from object that implement Read trait
//!
//! # Examples:
//! ```rust
//! use utf8_reader::Utf8Reader;
//! use std::io::Cursor;
//! use std::io::Write;
//!
//! let mut buf = Cursor::new(Vec::new());
//! buf.write("复/d❤".as_bytes()).unwrap();
//! buf.set_position(0);
//!
//! let mut reader = Utf8Reader::new(buf);
//!
//! assert_eq!(Some('复'.into()), reader.next());
//! assert_eq!(Some('/'.into()), reader.next());
//! assert_eq!(Some('d'.into()), reader.next());
//! assert_eq!(Some('❤'.into()), reader.next());
//! assert_eq!(None, reader.next());
//! ```

use std::convert::AsRef;
use std::convert::From;
use std::fmt;
use std::io::Read;
use std::iter::Iterator;
use std::str::FromStr;

macro_rules! impl_eq {
    ($lhs: ty, $rhs: ty) => {
        impl PartialEq<$rhs> for $lhs {
            fn eq(&self, other: &$rhs) -> bool {
                self.as_str() == other
            }
        }

        impl PartialEq<$lhs> for $rhs {
            fn eq(&self, other: &$lhs) -> bool {
                other.as_str() == self
            }
        }
    };
}

/// representing a UTF-8 character
///
/// Note: a UTF-8 character inside UTF8Char indicates an array [u8; 4]
/// so if an UTF-8 charactor's length of byte greater than 4 is not allow. e.g. ❤️ is 6 bytes length
#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub struct Utf8Char([u8; 4]);

impl Utf8Char {
    /// Extracts a byte slice containing the UTF-8 bytes
    pub fn as_slice(&self) -> &[u8] {
        match self.0 {
            [0, 0, 0, 0] | [0, 0, 0, _] => &self.0[3..],
            [0, 0, _, _] => &self.0[2..],
            [0, _, _, _] => &self.0[1..],
            _ => &self.0[..],
        }
    }

    /// Extracts a byte slice containing the UTF-8 bytes
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }

    /// Return `true` if this char is `white_space`
    ///
    /// `white_space` includes ` `, `\t`, `\r`, `\n`
    pub fn is_whitespace(&self) -> bool {
        match self.0 {
            [0, 0, 0, 9] | [0, 0, 0, 10] | [0, 0, 0, 13] | [0, 0, 0, 32] => true,
            _ => false,
        }
    }

    /// Check if the value is an ASCII decimal digit
    ///
    /// 0 to 9
    pub fn is_ascii_digit(&self) -> bool {
        match self.0 {
            [0, 0, 0, v] if v >= b'0' && v <= b'9' => true,
            _ => false,
        }
    }

    /// Return `true` if this char is an `Alphabetic`
    pub fn is_alphabetic(&self) -> bool {
        match self.0 {
            [0, 0, 0, v] if v >= b'A' && v <= b'Z' || v >= b'a' && v <= b'z' => true,
            _ => false,
        }
    }

    /// convert a UTF8Char to a digit
    ///
    /// diget as defined to be only the 0-9
    ///
    /// # Error
    /// Returns [Nane] if the UTF8Char does not refer to a digit
    pub fn to_digit(&self) -> Option<u32> {
        match self.0 {
            [0, 0, 0, v] if v >= b'0' && v <= b'9' => Some((v - b'0').into()),
            _ => None,
        }
    }
}

impl From<u8> for Utf8Char {
    fn from(value: u8) -> Self {
        Self([0, 0, 0, value])
    }
}

impl From<u32> for Utf8Char {
    fn from(value: u32) -> Self {
        Self(value.to_be_bytes())
    }
}

impl From<char> for Utf8Char {
    fn from(value: char) -> Self {
        let mut b = [0; 4];
        let st = value.encode_utf8(&mut b);
        let st = st.as_bytes();
        let mut b = [0; 4];
        for (i, v) in ((4 - st.len())..4).enumerate() {
            b[v] = st[i];
        }

        Self(b)
    }
}

impl fmt::Display for Utf8Char {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            String::from_str(self.as_str()).expect("cannot convert to a String")
        )
    }
}

impl AsRef<str> for Utf8Char {
    fn as_ref(&self) -> &str {
        use std::str;
        str::from_utf8(self.as_slice())
            .expect("cannot convert to a str, maybe is not a valid UTF-8 character")
    }
}

impl PartialEq<&str> for Utf8Char {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl PartialEq<Utf8Char> for &str {
    fn eq(&self, other: &Utf8Char) -> bool {
        other.as_str() == *self
    }
}

impl_eq!(Utf8Char, str);
impl_eq!(&Utf8Char, str);

/// Readd UTF-8 characters from object that implement Read
///
/// This is not validate the content whether it is a valid UTF-8 format or not
/// Implemented [Iterator]
///
/// # Example:
///
/// ```rust
/// # use utf8_reader::Utf8Reader;
/// # use std::io::Cursor;
/// # use std::io::Write;
///
/// let mut buf = Cursor::new(Vec::new());
/// buf.write("复/d❤".as_bytes()).unwrap();
/// buf.set_position(0);
///
/// let mut reader = Utf8Reader::new(buf);
///
/// assert_eq!(Some('复'.into()), reader.next());
/// assert_eq!(Some('/'.into()), reader.next());
/// assert_eq!(Some('d'.into()), reader.next());
/// assert_eq!(Some('❤'.into()), reader.next());
/// assert_eq!(None, reader.next());
/// ```
pub struct Utf8Reader<T: Read>(T);

impl<T: Read> Utf8Reader<T> {
    /// Create a new Utf8Reader
    ///
    /// # Argement:
    /// inner: object that implemented Read
    ///
    /// # Example:
    ///
    pub fn new(inner: T) -> Self {
        Self(inner)
    }
}

impl<T: Read> Iterator for Utf8Reader<T> {
    type Item = Utf8Char;

    fn next(&mut self) -> Option<Self::Item> {
        let mut b = [0u8; 1];
        let size = self.0.read(&mut b).expect("read a byte faied");
        if size == 0 {
            return None;
        }

        let first_byte = b[0];
        if first_byte < 128 {
            return Some(first_byte.into());
        }

        let utf8_32 = match first_byte & 0b11100000 {
            0b11110000 => exact_next(&mut self.0, 3, first_byte),
            0b11100000 => exact_next(&mut self.0, 2, first_byte),
            0b11000000 => exact_next(&mut self.0, 1, first_byte),
            _ => first_byte as u32,
        };

        Some(utf8_32.into())
    }
}

fn exact_next(read: &mut impl Read, count: usize, first_byte: u8) -> u32 {
    let mut b = [0u8; 1];
    let mut res_u32 = first_byte as u32;

    for _ in 0..count {
        let size = read.read(&mut b).expect("read a byte faied");
        if size != 0 {
            res_u32 = res_u32 << 8 | b[0] as u32;
        }
    }

    res_u32
}

#[cfg(test)]
mod test {
    use super::*;
    use std::io::Cursor;
    use std::io::Write;

    #[test]
    fn test_whitespace() {
        let mut buf = Cursor::new(Vec::new());
        buf.write(" d\t\r\n".as_bytes()).unwrap();
        buf.set_position(0);

        let mut r = Utf8Reader::new(buf);
        assert!(r.next().unwrap().is_whitespace());
        assert!(!r.next().unwrap().is_whitespace());
        assert!(r.next().unwrap().is_whitespace());
        assert!(r.next().unwrap().is_whitespace());
        assert!(r.next().unwrap().is_whitespace());
        assert!(r.next().is_none());
    }

    #[test]
    fn test_digit() {
        let mut buf = Cursor::new(Vec::new());
        buf.write("0123456789abi".as_bytes()).unwrap();
        buf.set_position(0);

        let mut r = Utf8Reader::new(buf);
        assert!(r.next().unwrap().is_ascii_digit());
        assert!(r.next().unwrap().is_ascii_digit());
        assert!(r.next().unwrap().is_ascii_digit());
        assert!(r.next().unwrap().is_ascii_digit());
        assert!(r.next().unwrap().is_ascii_digit());
        assert!(r.next().unwrap().is_ascii_digit());
        assert!(r.next().unwrap().is_ascii_digit());
        assert!(r.next().unwrap().is_ascii_digit());
        assert!(r.next().unwrap().is_ascii_digit());
        assert!(r.next().unwrap().is_ascii_digit());
        assert!(!r.next().unwrap().is_ascii_digit());
        assert!(!r.next().unwrap().is_ascii_digit());
        assert!(!r.next().unwrap().is_ascii_digit());
        assert!(r.next().is_none());
    }

    #[test]
    fn test_to_digit() {
        let mut buf = Cursor::new(Vec::new());
        buf.write("0123456789abi".as_bytes()).unwrap();
        buf.set_position(0);

        let mut r = Utf8Reader::new(buf);
        assert_eq!(Some(0), r.next().unwrap().to_digit());
        assert_eq!(Some(1), r.next().unwrap().to_digit());
        assert_eq!(Some(2), r.next().unwrap().to_digit());
        assert_eq!(Some(3), r.next().unwrap().to_digit());
        assert_eq!(Some(4), r.next().unwrap().to_digit());
        assert_eq!(Some(5), r.next().unwrap().to_digit());
        assert_eq!(Some(6), r.next().unwrap().to_digit());
        assert_eq!(Some(7), r.next().unwrap().to_digit());
        assert_eq!(Some(8), r.next().unwrap().to_digit());
        assert_eq!(Some(9), r.next().unwrap().to_digit());
        assert_eq!(None, r.next().unwrap().to_digit());
        assert_eq!(None, r.next().unwrap().to_digit());
        assert_eq!(None, r.next().unwrap().to_digit());
        assert_eq!(None, r.next());
    }

    #[test]
    fn is_alphabetic() {
        let mut buf = Cursor::new(Vec::new());
        buf.write("abcdABCDEZz0000".as_bytes()).unwrap();
        buf.set_position(0);

        let mut r = Utf8Reader::new(buf);
        assert!(r.next().unwrap().is_alphabetic());
        assert!(r.next().unwrap().is_alphabetic());
        assert!(r.next().unwrap().is_alphabetic());
        assert!(r.next().unwrap().is_alphabetic());
        assert!(r.next().unwrap().is_alphabetic());
        assert!(r.next().unwrap().is_alphabetic());
        assert!(r.next().unwrap().is_alphabetic());
        assert!(r.next().unwrap().is_alphabetic());
        assert!(r.next().unwrap().is_alphabetic());
        assert!(r.next().unwrap().is_alphabetic());
        assert!(r.next().unwrap().is_alphabetic());
        assert!(!r.next().unwrap().is_alphabetic());
        assert!(!r.next().unwrap().is_alphabetic());
        assert!(!r.next().unwrap().is_alphabetic());
        assert!(!r.next().unwrap().is_alphabetic());
        assert!(r.next().is_none());
    }

    #[test]
    fn test_display() {
        let mut buf = Cursor::new(Vec::new());
        buf.write("复// d".as_bytes()).unwrap();
        buf.set_position(0);

        let mut r = Utf8Reader::new(buf);
        assert_eq!("复".to_string(), r.next().unwrap().to_string());
        assert_eq!("/".to_string(), r.next().unwrap().to_string());
    }

    #[test]
    fn test_as_str() {
        let mut buf = Cursor::new(Vec::new());
        buf.write("复// d".as_bytes()).unwrap();
        buf.set_position(0);

        let mut r = Utf8Reader::new(buf);
        let utf8char = r.next().unwrap();
        assert_eq!("复", utf8char.as_ref());
        let utf8char = r.next().unwrap();
        assert_eq!("/", utf8char.as_ref());
        let utf8char = r.next().unwrap();
        assert_eq!("/", utf8char.as_ref());
        let utf8char = r.next().unwrap();
        assert_eq!(" ", utf8char.as_ref());
        let utf8char = r.next().unwrap();
        assert_eq!("d", utf8char.as_ref());
        assert_eq!(None, r.next());
    }

    #[test]
    fn test_iterator() {
        let mut buf = Cursor::new(Vec::new());
        buf.write(
            r"复// d❤
1+1=2 // é异"
                .as_bytes(),
        )
        .unwrap();
        buf.set_position(0);

        let mut r = Utf8Reader::new(buf);

        assert_eq!(Some('复'.into()), r.next());
        assert_eq!(Some('/'.into()), r.next());
        assert_eq!(Some('/'.into()), r.next());
        assert_eq!(Some(' '.into()), r.next());
        assert_eq!(Some('d'.into()), r.next());
        assert_eq!(Some('❤'.into()), r.next());
        assert_eq!(Some('\n'.into()), r.next());
        assert_eq!(Some('1'.into()), r.next());
        assert_eq!(Some('+'.into()), r.next());
        assert_eq!(Some('1'.into()), r.next());
        assert_eq!(Some('='.into()), r.next());
        assert_eq!(Some('2'.into()), r.next());
        assert_eq!(Some(' '.into()), r.next());
        assert_eq!(Some('/'.into()), r.next());
        assert_eq!(Some('/'.into()), r.next());
        assert_eq!(Some(' '.into()), r.next());
        assert_eq!(Some('é'.into()), r.next());
        assert_eq!(Some('异'.into()), r.next());
        assert_eq!(None, r.next());
    }

    #[test]
    fn wrong_character() {
        let mut buf = Cursor::new(Vec::new());
        buf.write("\u{D7FF}复".as_bytes()).unwrap();
        buf.set_position(0);

        let mut r = Utf8Reader::new(buf);
        assert_eq!(Some('\u{D7FF}'.into()), r.next());
        assert_eq!(Some('复'.into()), r.next());
        assert_eq!(None, r.next());
    }

    #[test]
    fn equal_str() {
        let mut buf = Cursor::new(Vec::new());
        buf.write("0a/*-比".as_bytes()).unwrap();
        buf.set_position(0);

        let mut r = Utf8Reader::new(buf);
        let v = r.next().unwrap();
        assert_eq!("0", v);
        assert_eq!("0", &v);
        assert_eq!("a", r.next().unwrap());
        assert_eq!("/", r.next().unwrap());
        assert_eq!("*", r.next().unwrap());
        assert_eq!("-", r.next().unwrap());
        assert_eq!(r.next().unwrap(), "比");
        assert_eq!(None, r.next());
    }
}
