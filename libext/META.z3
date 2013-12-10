# Specifications for the "z3" library:
description = "Z3 theorem prover"
version = "4.3.2-ml-ng"
directory = ""
archive(byte) = "z3.cma"
archive(native) = "z3.cmxa"
linkopts = "-cclib -lstdc++ -cclib -lz3"

package "z3enums"
(
  requires = "z3"
  version = "4.3.2-ml-ng"
  archive(native) = "z3enums.cmxa"
  archive(byte) = "z3enums.cma"
  linkopts = "-cclib -lz3enums"
)
