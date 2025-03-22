# p2d
p2d compiles pseudo-boolean constraints in a d-DNNF

# running
`p2d /file.opb -m ddnnf -o file.nnf` to compile a d-DNNF.
`p2d /file.opb -m mc` to perform model counting.

# building
p2d depends on the patoh library but can not directly include it due to licensing issues. Download [patoh](https://faculty.cc.gatech.edu/~umit/software.html) and put the patoh directory in a lib directory (directly in the project root). Read the license of patoh and check if you comply to it.
run `cargo build --release` to build the project
