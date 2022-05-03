# Trinket
### *(**T**ables and **R**ecords **IN**cluding **KE**y **T**ooling)*

![A profile view of a cute, slightly smiling trinket snake](assets/trinket.jpg)  
Image source: [Arupananda Rao on Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Close_Up_of_A_Common_Trinket.JPG) ([link to the 640px version used](https://upload.wikimedia.org/wikipedia/commons/thumb/6/6b/Close_Up_of_A_Common_Trinket.JPG/640px-Close_Up_of_A_Common_Trinket.JPG))

## Requirements
* NASM 2.15+  
Need at least [v2.15](https://nasm.us/doc/nasmdocc.html#section-C.1.6) because we use the MASM-type DUP pseudo-instructions (e.g., `db`) for storing strings to access from the runtime.
  * Reference: [NASM documentation section 3.2.1](https://nasm.us/doc/nasmdoc3.html#section-3.2.1)
  * Installation:
    Currently, NASM 2.15 has been built for some versions of Ubuntu, but only listed on `apt` for versions past Focal. The binary is compatible with Focal and can be found [here](http://launchpadlibrarian.net/504311363/nasm_2.15.05-1_amd64.deb). To install, run `sudo apt install ./nasm_2.15.05-1_amd64.deb` from the containing directory.

## Design decisions/notes
### Records
* New SNAKEVAL, tag `0x0000000000000003`
* Immutable
* Did same trick as `ELetRec` -> use the `binding` expr type but in `is_well_formed` restrict it to only `BName`s
* Well-formedness also ensures:
  * No duplicate field names within a record
  * No `BBlank` or `BTuple` binds in records
* New errors: `RecordFieldNotName`, `RecordDuplicateField`
* Extended `naive_stack_allocation` to also return an env mapping field names to ids (integers),
    had to change code gen to take in this information
* Changed `print` in runtime to support printing records, including the string field names
* Can access a field of a record by field name with the "dot-fieldname" syntax: "let zz = {afield = 1, b = 2} in zz.afield"
* The field access operator is left-associative
* Runtime error err_GET_FIELD_NOT_RECORD (19) if try to access field of a non-record SNAKEVAL
* Runtime error err_GET_FIELD_NOT_FOUND (20) if try to get the value of a field which is not present in the record
* Structural (ie. equal(), runtime) equality of 2 records means: same fields in same order with same values
