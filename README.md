# utf8_reader

Read utf-8 characters from object that implement Read trait

# Usage

```rust
use utf8_reader::Utf8Reader;
use std::io::Cursor;
use std::io::Write;

let mut buf = Cursor::new(Vec::new());
buf.write("复/d❤".as_bytes()).unwrap();
buf.set_position(0);

let mut reader = Utf8Reader::new(buf);

assert_eq!(Some('复'.into()), reader.next());
assert_eq!(Some('/'.into()), reader.next());
assert_eq!(Some('d'.into()), reader.next());
assert_eq!(Some('❤'.into()), reader.next());
assert_eq!(None, reader.next());
```

Note: This Utf8Reader would not validate whether the content is a valid UTF-8