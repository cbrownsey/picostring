#![warn(clippy::pedantic)]
use core::{fmt::Display, mem::MaybeUninit, ptr};
use std::{borrow::Borrow, hash::Hash};

/// A stack allocated string containing up to CAPACITY bytes. Currently that must be strictly
/// less than 64, but the utf-8 3 and 4 width extension bytes may be used to increase this to
/// 2048, or 32,768 which seems a tad extravagant.
///
// / Additionally, the check for maximum CAPACITY is checked at compile time. This check only
// / happens if the PicoString is actually initialized, so simply having a type variable with
// / `type A = PicoString<64>` will compile, but calling `A::new()` will result in a compile
// / error.
///
/// # Safety
/// The last two bytes must be initialized, and the final byte must contain a
/// value in the range 0xC0..=0xFF. The first `len` bytes must contain an
/// initialized and valid utf-8 string.
#[derive(Clone, Copy)]
pub struct PicoString<const CAPACITY: usize>([MaybeUninit<u8>; CAPACITY]);

impl<const N: usize> PicoString<N> {
    // Since the bytes in the range 0xC0..=0xFF are either invalid bytes, or
    // used as the beginnings of multibyte sequences, they can never occur as
    // the last byte of a utf-8 string.
    const FINAL_BYTE_MIN: u8 = 0xC0;
    // const SECOND_FINAL_BYTE_MIN: u8 = 0xE0;

    /// The maximum capacity that this struct could possibly hold.
    const MAX_CAPACITY: usize = 64;

    #[doc(hidden)]
    #[allow(unused)]
    const COMPILE_GATE: () = assert!(
        N <= Self::MAX_CAPACITY,
        "PicoString must have capacity less than or equal to 64"
    );

    /// Create a new instance of `PicoString`.
    ///
    /// # Panics
    ///
    /// Panics if this functions is somehow run on a `PicoString<N>` with N greater than 64. This
    /// should be impossible however due to a compile time check.
    pub fn new() -> Self {
        const UNINIT: MaybeUninit<u8> = MaybeUninit::uninit();
        // Self::COMPILE_GATE;

        assert!(
            N <= Self::MAX_CAPACITY,
            "PicoString may only hold up to {} bytes.",
            Self::MAX_CAPACITY
        );
        // if N > Self::MAX_CAPACITY {
        //     panic!(
        //         "PicoString may only hold up to {} bytes.",
        //         Self::MAX_CAPACITY
        //     );
        // };

        let mut arr = [UNINIT; N];

        if N > 0 {
            arr[N - 1].write(Self::FINAL_BYTE_MIN);
        }

        Self(arr)
    }

    /// Checks to see if adding `len` bytes to the `PicoString` would overflow it.
    pub fn could_fit(&self, len: usize) -> bool {
        self.len() + len <= N
    }

    /// Inserts a character into the `PicoString` at a byte position, returning false if the
    /// additional character cannot fit.
    ///
    /// This is an *O*(*n*) operation as it requires copying every element in the buffer past
    /// the byte position.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `PicoString`'s length, if it does not lie on a `char`
    /// boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// # use picostring::PicoString;
    /// let mut s = PicoString::<3>::new();
    ///
    /// assert!(s.insert(0, 'o'), "a");
    /// assert!(s.insert(0, 'f'), "b");
    /// assert!(s.insert(2, 'o'), "c");
    ///
    /// assert_eq!("foo", s);
    /// ```
    pub fn insert(&mut self, idx: usize, c: char) -> bool {
        assert!(
            self.is_char_boundary(idx),
            "`idx` does not lie on a character boundary"
        );
        let mut bytes = [0u8; 4];
        let s_bytes = c.encode_utf8(&mut bytes).as_bytes();
        let new_len = self.len() + c.len_utf8();
        if new_len <= N {
            unsafe {
                self.insert_bytes_unchecked(idx, s_bytes);
                self.set_len(new_len);
            };
            true
        } else {
            false
        }
    }

    /// Inserts a string slice into the `PicoString` at a byte position, returning false if the
    /// additional string cannot fit.
    ///
    /// This is an *O*(*n*) operation as it requires copying every element in the buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `PicoString`'s length, if it does not lie on a `char`
    /// boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// # use picostring::PicoString;
    /// let mut s = PicoString::<6>::try_from("bar").unwrap();
    ///
    /// assert!(s.insert_str(0, "foo"));
    ///
    /// assert_eq!("foobar", s);
    /// ```
    pub fn insert_str(&mut self, idx: usize, s: &str) -> bool {
        assert!(
            self.is_char_boundary(idx),
            "`idx` does not lie on a character boundary"
        );
        let s_bytes = s.as_bytes();
        let new_len = self.len() + s.len();
        if new_len <= N {
            unsafe {
                self.insert_bytes_unchecked(idx, s_bytes);
                self.set_len(new_len);
            };
            true
        } else {
            false
        }
    }

    unsafe fn insert_bytes_unchecked(&mut self, idx: usize, bytes: &[u8]) {
        let ptr = self.as_mut_ptr().add(idx);
        let len_to_move = self.len() - idx;
        ptr::copy(ptr.add(idx), ptr.add(len_to_move), len_to_move);
        ptr::copy_nonoverlapping(bytes.as_ptr(), ptr, bytes.len());
    }

    /// Removes a `char` from this `PicoString` at a byte position and returns it.
    ///
    /// This is an *O*(*n*) operation, as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than or equal to the `String`'s length,
    /// or if it does not lie on a `char` boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use picostring::PicoString;
    /// let mut s = PicoString::<3>::try_from("foo").unwrap();
    ///
    /// assert_eq!(s.remove(0), 'f');
    /// assert_eq!(s.remove(1), 'o');
    /// assert_eq!(s.remove(0), 'o');
    /// ```
    pub fn remove(&mut self, idx: usize) -> char {
        let Some(ch) = self[idx..].chars().next() else {
            panic!("cannot remove a char from the end of a string");
        };
        // let ch = match self[idx..].chars().next() {
        //     Some(ch) => ch,
        //     None => panic!("cannot remove a char from the end of a string"),
        // };

        let next = idx + ch.len_utf8();
        let len = self.len();
        unsafe {
            ptr::copy(
                self.as_ptr().add(next),
                self.as_mut_ptr().add(idx),
                len - next,
            );
            self.set_len(len - ch.len_utf8());
        };
        ch
    }

    /// Truncates this `PicoString`, removing all contents.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// # use picostring::PicoString;
    /// let mut s = PicoString::<3>::try_from("foo").unwrap();
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(s.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        unsafe { self.set_len(0) }
    }

    /// Shortens this `PicoString` to the specified length.
    ///
    /// If `new_len` is greater than the string's current length, this has no
    /// effect.
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::from("hello");
    ///
    /// s.truncate(2);
    ///
    /// assert_eq!("he", s);
    /// ```
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            unsafe { self.set_len(new_len) }
        }
    }

    fn as_ptr(&self) -> *const u8 {
        ptr::addr_of!(self.0).cast()
    }

    fn as_mut_ptr(&mut self) -> *mut u8 {
        ptr::addr_of_mut!(self.0).cast()
    }

    #[must_use]
    pub fn len(&self) -> usize {
        match N {
            0 => 0,
            1..=64 => {
                let len_byte = unsafe { self.0[N - 1].assume_init() };
                if len_byte >= Self::FINAL_BYTE_MIN {
                    (len_byte - Self::FINAL_BYTE_MIN) as usize
                } else {
                    N
                }
            }
            _ => unreachable!(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Set the length of the `PicoString`. Notably, this should not touch the length byte, which is
    /// the last byte, if the new length would cause the string to overrun those bytes.
    ///
    /// # Safety
    /// New length must be less than or equal to the maximum length.
    unsafe fn set_len(&mut self, new_len: usize) {
        use core::cmp::Ordering;
        match new_len.cmp(&N) {
            Ordering::Less => {
                self.0[N - 1].write((new_len as u8) + Self::FINAL_BYTE_MIN);
            }
            Ordering::Equal => {}
            Ordering::Greater => {
                debug_assert!(false, "new length must be smaller than or equal to N");
                core::hint::unreachable_unchecked();
            }
        }
    }

    /// Appends the given byte to the PicoString
    ///
    /// # Safety
    ///
    /// The given bytes must never cause PicoString to contain a non-utf8 string,
    /// and a byte must not be pushed to a full PicoString.
    #[allow(dead_code)]
    unsafe fn push_byte(&mut self, byte: u8) {
        let curr_len = self.len();
        self.set_len(curr_len + 1);
        self.0.get_unchecked_mut(curr_len).write(byte);
    }

    unsafe fn push_slice_unchecked(&mut self, bytes: &[u8]) {
        let curr_len = self.len();
        self.set_len(curr_len + bytes.len());
        ptr::copy_nonoverlapping(bytes.as_ptr(), self.as_mut_ptr().add(curr_len), bytes.len());
    }

    unsafe fn push_slice(&mut self, bytes: &[u8]) -> bool {
        if self.len() + bytes.len() > N {
            false
        } else {
            self.push_slice_unchecked(bytes);
            true
        }
    }

    pub fn push_str(&mut self, s: &str) -> bool {
        unsafe { self.push_slice(s.as_bytes()) }
    }

    pub fn push(&mut self, c: char) -> bool {
        self.push_str(c.encode_utf8(&mut [0u8; 4]))
    }

    pub fn pop(&mut self) -> Option<char> {
        let c = self.as_str().chars().next_back()?;
        unsafe { self.set_len(self.len() - c.len_utf8()) };
        Some(c)
    }

    /// Returns a byte slice of this `PicoString`'s contents.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// # use picostring::PicoString;
    /// let s = PicoString::<5>::try_from("hello").unwrap();
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    /// ```
    pub fn as_bytes(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    /// Get the contents of the `PicoString` as a mutable byte slice.
    ///
    /// # Safety
    ///
    /// The returned slice must never be modified such that it is no longer a valid utf8 sequence.
    pub unsafe fn as_bytes_mut(&mut self) -> &mut [u8] {
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }

    /// Extracts a string slice containing the entire `PicoString`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// # use picostring::PicoString;
    /// let s = PicoString::<0>::try_from("").unwrap();
    /// ```
    pub fn as_str(&self) -> &str {
        unsafe { core::str::from_utf8_unchecked(self.as_bytes()) }
    }

    /// Converts a `PicoString` into a mutable string slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// # use picostring::PicoString;
    /// let mut s = PicoString::<6>::try_from("foobar").unwrap();
    /// let s_mut_str = s.as_mut_str();
    ///
    /// s_mut_str.make_ascii_uppercase();
    ///
    /// assert_eq!("FOOBAR", s_mut_str);
    /// ```
    pub fn as_mut_str(&mut self) -> &mut str {
        unsafe { core::str::from_utf8_unchecked_mut(self.as_bytes_mut()) }
    }
}

impl<const N: usize> core::ops::Deref for PicoString<N> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const N: usize> core::ops::DerefMut for PicoString<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_str()
    }
}

impl<const N: usize> Default for PicoString<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> TryFrom<&str> for PicoString<N> {
    type Error = ExceedsCapacity;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        if value.len() > N {
            Err(ExceedsCapacity(value.len(), N))
        } else {
            let mut s = PicoString::new();
            s.push_str(value);
            Ok(s)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExceedsCapacity(usize, usize);

impl Display for ExceedsCapacity {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "string of size {} can't fit into capacity {}",
            self.0, self.1
        )
    }
}

impl std::error::Error for ExceedsCapacity {}

impl<const N: usize, const M: usize> PartialEq<PicoString<M>> for PicoString<N> {
    fn eq(&self, other: &PicoString<M>) -> bool {
        self.as_str().eq(other.as_str())
    }
}

impl<const N: usize> Eq for PicoString<N> {}

impl<const N: usize, const M: usize> PartialOrd<PicoString<M>> for PicoString<N> {
    fn partial_cmp(&self, other: &PicoString<M>) -> Option<std::cmp::Ordering> {
        Some(self.as_str().cmp(other.as_str()))
    }
}

impl<const N: usize> Ord for PicoString<N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_str().cmp(&other.as_str())
    }
}

impl<const N: usize> core::fmt::Debug for PicoString<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(self.as_str(), f)
    }
}

impl<const N: usize> core::fmt::Display for PicoString<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(self.as_str(), f)
    }
}

impl<const N: usize> From<PicoString<N>> for String {
    fn from(value: PicoString<N>) -> Self {
        String::from(&*value)
    }
}

impl<const N: usize> AsRef<str> for PicoString<N> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<const N: usize> AsMut<str> for PicoString<N> {
    fn as_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<const N: usize> Borrow<str> for PicoString<N> {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl<const N: usize> AsRef<[u8]> for PicoString<N> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const N: usize> Hash for PicoString<N> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

#[cfg(feature = "serde")]
impl<const N: usize> serde::Serialize for PicoString<N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&*self)
    }
}

#[cfg(feature = "serde")]
impl<'de, const N: usize> serde::Deserialize<'de> for PicoString<N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct StrVisitor<const N: usize>;

        impl<const N: usize> serde::de::Visitor<'_> for StrVisitor<N> {
            type Value = PicoString<N>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_fmt(format_args!(
                    "a string of length less than or equal to {}",
                    N
                ))
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                PicoString::try_from(v).map_err(|e| E::custom(e.to_string()))
            }
        }

        deserializer.deserialize_str(StrVisitor::<N>)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn ptr_methods() {
        let mut s = PicoString::<1>::new();
        let v: u8 = unsafe { ptr::read(s.as_ptr()) };
        assert_eq!(v, 0xC0);
        assert_eq!(s.as_ptr(), s.as_mut_ptr());
    }

    #[test]
    fn unsafe_set_len() {
        use core::slice;
        let mut s = PicoString::<2>::new();
        assert_eq!(s.len(), 0);
        s.0[0].write(b'A');
        unsafe { s.set_len(1) };
        assert_eq!(s.len(), 1);
        s.0[1].write(b'B');
        assert_eq!(s.len(), 2);
        unsafe { s.set_len(2) };
        assert_eq!(s.len(), 2);
        let bstr = unsafe { slice::from_raw_parts(s.as_ptr(), 2) };
        assert_eq!(bstr, b"AB");
    }

    #[test]
    fn unsafe_push_byte() {
        use core::slice;
        let mut s = PicoString::<3>::new();
        assert_eq!(s.len(), 0);
        unsafe { s.push_byte(b'A') };
        assert_eq!(s.len(), 1);
        let bstr = unsafe { slice::from_raw_parts(s.as_ptr(), 1) };
        assert_eq!(bstr, b"A");
        unsafe { s.push_byte(b'B') };
        assert_eq!(s.len(), 2);
        let bstr = unsafe { slice::from_raw_parts(s.as_ptr(), 2) };
        assert_eq!(bstr, b"AB");
        unsafe { s.push_byte(b'C') };
        assert_eq!(s.len(), 3);
        let bstr = unsafe { slice::from_raw_parts(s.as_ptr(), 3) };
        assert_eq!(bstr, b"ABC");
    }

    #[test]
    pub fn as_slice() {
        let mut s = PicoString::<3>::new();
        assert_eq!(s.len(), 0);
        unsafe { s.push_byte(b'A') };
        assert_eq!(s.as_bytes(), b"A");
        unsafe { s.push_byte(b'D') };
        assert_eq!(s.as_bytes(), b"AD");
        unsafe { s.push_byte(b'C') };
        assert_eq!(s.as_bytes(), b"ADC");
        unsafe { s.as_bytes_mut()[1] = b'B' };
        assert_eq!(s.as_bytes(), b"ABC");
    }

    #[test]
    pub fn unsafe_push_slice_unchecked() {
        let mut s = PicoString::<5>::new();
        assert_eq!(s.as_bytes(), b"");
        unsafe { s.push_slice_unchecked(b"A") };
        assert_eq!(s.as_bytes(), b"A");
        unsafe { s.push_slice_unchecked(b"BCD") };
        assert_eq!(s.as_bytes(), b"ABCD");
        unsafe { s.push_slice_unchecked(b"E") };
        assert_eq!(s.as_bytes(), b"ABCDE");
    }

    #[test]
    pub fn unsafe_push_slice() {
        let mut s = PicoString::<5>::new();
        assert!(unsafe { s.push_slice(b"AB") });
        assert_eq!(s.as_bytes(), b"AB");
        assert!(!unsafe { s.push_slice(b"CDEF") });
        assert_eq!(s.as_bytes(), b"AB");
        assert!(unsafe { s.push_slice(b"CDE") });
        assert_eq!(s.as_bytes(), b"ABCDE");
    }

    #[test]
    pub fn push_str_char() {
        let mut s = PicoString::<8>::new();
        assert!(s.push('A'));
        assert!(s.push('β'));
        assert_eq!(s.as_str(), "Aβ");
        assert_eq!(s.len(), 3);
        assert!(!s.push_str("CDEFGH"));
        assert!(s.push_str("CDEF"));
        assert_eq!(s.len(), 7);
        assert!(!s.push('Γ'));
        assert!(s.push('G'));
        assert_eq!(s.as_str(), "AβCDEFG");
    }

    #[test]
    pub fn pop_char() {
        let mut s = PicoString::<6>::try_from("ABCΔE").unwrap();
        assert_eq!(s.len(), 6);
        assert_eq!(s.pop(), Some('E'));
        assert_eq!(s.as_str(), "ABCΔ");
        assert_eq!(s.pop(), Some('Δ'));
        assert_eq!(s.as_str(), "ABC");
        assert_eq!(s.pop(), Some('C'));
        assert_eq!(s.pop(), Some('B'));
        assert_eq!(s.pop(), Some('A'));
        assert_eq!(s.as_str(), "");
        assert_eq!(s.pop(), None);
    }

    #[test]
    pub fn try_from() {
        assert_eq!(&*PicoString::<0>::try_from("").unwrap(), "");
        assert_eq!(&*PicoString::<1>::try_from("A").unwrap(), "A");
        assert_eq!(&*PicoString::<2>::try_from("AB").unwrap(), "AB");

        assert!(PicoString::<0>::try_from("A").is_err());
        assert!(PicoString::<1>::try_from("AB").is_err());
    }

    #[test]
    pub fn test_on_all_chars() {
        for c in '\0'..=char::MAX {
            let mut s0 = PicoString::<0>::new();
            let mut s1 = PicoString::<1>::new();
            let mut s2 = PicoString::<2>::new();
            let mut s3 = PicoString::<3>::new();
            let mut s4 = PicoString::<4>::new();

            match c.len_utf8() {
                1 => {
                    assert!(!s0.push(c));
                    assert!(s1.push(c));
                    assert!(s2.push(c));
                    assert!(s3.push(c));
                    assert!(s4.push(c));
                }
                2 => {
                    assert!(!s0.push(c));
                    assert!(!s1.push(c));
                    assert!(s2.push(c));
                    assert!(s3.push(c));
                    assert!(s4.push(c));
                }
                3 => {
                    assert!(!s0.push(c));
                    assert!(!s1.push(c));
                    assert!(!s2.push(c));
                    assert!(s3.push(c));
                    assert!(s4.push(c));
                }
                4 => {
                    assert!(!s0.push(c));
                    assert!(!s1.push(c));
                    assert!(!s2.push(c));
                    assert!(!s3.push(c));
                    assert!(s4.push(c));
                }
                _ => unreachable!(),
            }
        }
    }

    #[test]
    fn max_len_picostring() {
        const S: &str = "ABCDEFGHIJKLMNOPQRSTUVWXYZ012345";
        assert_eq!(S.len(), 32);
        let mut s = PicoString::<64>::new();
        s.push_str(S);
        assert_eq!(s.len(), 32);
        s.push_str(S);
        assert_eq!(s.len(), 64);
        assert_eq!(s.pop(), Some('5'));
        assert_eq!(s.len(), 63);
    }
}
