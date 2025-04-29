A fixed capacity, stack allocated, const generic based string. Can't outgrow it's given capacity, and always occupies exactly `CAPACITY` bytes, with no need for another byte to store the length.

# Why

This library is a proof of concept for space-optimized, stack allocated strings for domains where typical strings would only need some small number of bytes (e.g 4 or 8 to fit perfectly into a register), and adding another byte to store length increases the total size of the string by a not insignificant percentage.

Benchmarking is of course needed to determine if the overhead of calculating the length is worth it, or if having some bytes dedicated to length ends up being faster regardless. Either way, my perfectionist tendencies are satiated and this project is good enough to be used as an internal dependancy for a project I'm working on.

# How

UTF-8 is [~~an encoding sent from god himself~~](http://utf8everywhere.org/) a variable-length encoding, which rust has made great use of by ensuring that all strings are correct and valid UTF-8. This means that no string in rust can contain any non-UTF-8 characters or any invalid UTF-8 bytes.

Given a fixed length array, the last byte will always be either a multibyte character start byte (of which there are 64), or the ending byte of a character. If it is an ending byte, then the string's length is the same as the array's length. If it isn't, we store the length of the string using one of the sixty-four start bytes.

# Should you use this?

Probably not. I hacked it together in the span of about 2 or 3 days, have done very little proper testing, and will probably immediately go into maintenance mode for the next few months.
