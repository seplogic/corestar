# Specifications for the "z3" library:
description = "Z3 theorem prover"
version = "4.3.2-ml-ng-e79e1830180c926e231d3c1c6411566e70c0de46"
directory = ""
archive(byte) = "z3.cma"
archive(native) = "z3.cmxa"
linkopts = "-cclib -lstdc++ -cclib -lz3"
