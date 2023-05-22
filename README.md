A fixed capacity, stack allocated, const generic based string. Can't outgrow it's given capacity, and always occupies exactly `CAPACITY` bytes, with no need for another byte to store the length.

# Why

Because I'm a cheap bastard who thinks it's important to penny-pinch bytes on his laptop with 8GB of RAM.

More seriously, it's a proof of concept for space-optimized, stack allocated strings for domains where typical strings would only need some small number of bytes (e.g 4 or 8 to fit perfectly into a register), and adding another byte to store length increases the total size of the string by a non-significant percentage.

Benchmarking is of course needed to determine if the overhead of calculating the length is worth it, or if having some bytes dedicated to length ends up being faster regardless. Either way, my perfectionist tendencies are satiated and this project is good enough to be used as an internal dependancy for a project I'm working on.

# How

UTF-8 is [~~an encoding sent from god himself~~](http://utf8everywhere.org/) a variable-length encoding, which rust has made great use of by ensuring that all strings are correct and valid utf-8. This means that no string in rust can contain any non-utf-8 characters or any invalid utf-8 bytes. This can be taken advantage of, as it is obvious that the last byte in an array cannot be valid utf-8 if it's also the start of a multi-byte character. Since there are 64 (0xC0..=0xFF), we can encode a full 64 values of length unambiguously (0-63 with leading bytes, 64th with any valid utf-8).

# Should you use this?

Probably not. I hacked it together in the span of about 2 or 3 days, have done very little proper testing, and will probably immediately go into maintenance mode for the next few months.
