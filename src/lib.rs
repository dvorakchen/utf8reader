//! Read UTF-8 characters from object that implement Read trait
//! 
//! # Examples:
//! ```rust
//! use utf8reader::Utf8Reader;
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

use std::convert::From;
use std::fmt;
use std::io::Read;
use std::iter::Iterator;

/// representing a UTF-8 character
///
/// Note: a UTF-8 character inside UTF8Char indicates an array [u8; 4]
/// so if an UTF-8 charactor's length of byte greater than 4 is not allow. e.g. ❤️ is 6 bytes length
#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub struct Utf8Char([u8; 4]);

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
        let mut tmp: Vec<u8> = self.0.clone().into_iter().filter(|v| *v != 0).collect();
        if tmp.len() == 0 {
            tmp.push(0);
        }

        write!(f, "{}", String::from_utf8(tmp).unwrap())
    }
}

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
        let size = self.0.read(&mut b).unwrap();
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
        let size = read.read(&mut b).unwrap();
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
    fn test_display() {
        let mut buf = Cursor::new(Vec::new());
        buf.write(
            r"复// d复
1+1=2 // 诡异"
                .as_bytes(),
        )
        .unwrap();
        buf.set_position(0);

        let mut r = Utf8Reader::new(buf);
        let u8char = r.next().unwrap();
        assert_eq!("复".to_string(), u8char.to_string());
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
}
