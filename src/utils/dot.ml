(********************************************************
   This file is part of coreStar
        src/utils/dot.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

let esc_nl_re = Str.regexp "\\\\n"

let escape_for_label s =
  Str.global_replace esc_nl_re "\\l" (String.escaped s)

