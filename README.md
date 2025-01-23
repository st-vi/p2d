# p2d
p2d compiles pseudo-boolean constraints in a d-DNNF

# building
p2d depends on the patoh library but can not directly include it due to licensing issues. Download [patoh](https://faculty.cc.gatech.edu/~umit/software.html) and put the patoh directory in the lib directory. Read the license of patoh and check if you comply to it.
run cargo build --release
