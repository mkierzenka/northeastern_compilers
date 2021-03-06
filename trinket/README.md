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
* Can access a field of a record by field name with the "dot-fieldname" syntax: `let zz = {afield = 1, b = 2} in zz.afield`
* The field access operator is left-associative
* Runtime error `err_GET_FIELD_NOT_RECORD` (19) if try to access field of a non-record SNAKEVAL
* Runtime error `err_GET_FIELD_NOT_FOUND` (20) if try to get the value of a field which is not present in the record
* Structural equality of 2 records means: same fields in same order with same values (see `main.c`'s `equal` function)
* `isrecord(...)` built-in, with the usual behavior/semantics

### Tables
* New SNAKEVAL, tag `0x0000000000000009`. This meant we had to expand to use 4-bit tags for booleans, closures, records, and tables.
* Immutable
* A comma-separated list of exprs (rows), each of which should be a record at runtime
* Create one by wrapping the list in `(|` and `|)`
* Note, there can technically be arbitrary whitespace between the parentheses and the pipes because we decided to
  not spend so much time fighting with the parser
* The first record/row defines the fields of the table, table creation includes validating that all records have same field names in same order as the first
* Structural equality of 2 tables means: same records in same order
* Table creation (and record equality) may later move to accepting records with the same fields but differently ordered
* Empty tables are written as `(| |)` (whitespace between ends required)
* Empty tables are printed as `(empty table)`
* Nested non-empty tables (within tables or records) are printed as `(non-empty table)` for brevity/slightly better formatting
* Tables are printed/returned in a simple tab character-based format with column names across the top, e.g.,
```
table:
    field1  field2  field3
0   17      103     false
1   2       1337    true
```
* New runtime functions, hidden to the user but helpful to us: `checkFields` (are the same fields present in same order?), `printRecordFieldsAsRow`, `printRecordValuesAsRow`
