procedure c:
  {emp} () {emp}
procedure b:
  {@s=2} (@s) {false||@s=1||@s=3}
  {emp*@s!=2} () {emp}
procedure a:
  {@s=1} (@s) {false||@s=1||@s=2}
  {emp*@s!=1} () {emp}

procedure seq_:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
?

procedure seq_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_(); call c();

procedure seq_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_(); call b();

procedure seq_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_(); call a();

procedure seq_c_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c(); call c();

procedure seq_b_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b(); call c();

procedure seq_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a(); call c();

procedure seq_c_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c(); call b();

procedure seq_b_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b(); call b();

procedure seq_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a(); call b();

procedure seq_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c(); call a();

procedure seq_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b(); call a();

procedure seq_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a(); call a();

procedure seq_c_c_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_c(); call c();

procedure seq_b_c_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_c(); call c();

procedure seq_a_c_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_c(); call c();

procedure seq_c_b_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_b(); call c();

procedure seq_b_b_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_b(); call c();

procedure seq_a_b_c:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_b(); call c();

procedure seq_c_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_a(); call c();

procedure seq_b_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_a(); call c();

procedure seq_a_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_a(); call c();

procedure seq_c_c_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_c(); call b();

procedure seq_b_c_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_c(); call b();

procedure seq_a_c_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_c(); call b();

procedure seq_c_b_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_b(); call b();

procedure seq_b_b_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_b(); call b();

procedure seq_a_b_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_b(); call b();

procedure seq_c_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_a(); call b();

procedure seq_b_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_a(); call b();

procedure seq_a_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_a(); call b();

procedure seq_c_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_c(); call a();

procedure seq_b_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_c(); call a();

procedure seq_a_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_c(); call a();

procedure seq_c_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_b(); call a();

procedure seq_b_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_b(); call a();

procedure seq_a_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_b(); call a();

procedure seq_c_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_a(); call a();

procedure seq_b_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_a(); call a();

procedure seq_a_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_a(); call a();

procedure seq_c_c_c_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_c_c(); call c();

procedure seq_b_c_c_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_c_c(); call c();

procedure seq_a_c_c_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_c_c(); call c();

procedure seq_c_b_c_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_b_c(); call c();

procedure seq_b_b_c_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_b_c(); call c();

procedure seq_a_b_c_c:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_b_c(); call c();

procedure seq_c_a_c_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_a_c(); call c();

procedure seq_b_a_c_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_a_c(); call c();

procedure seq_a_a_c_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_a_c(); call c();

procedure seq_c_c_b_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_c_b(); call c();

procedure seq_b_c_b_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_c_b(); call c();

procedure seq_a_c_b_c:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_c_b(); call c();

procedure seq_c_b_b_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_b_b(); call c();

procedure seq_b_b_b_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_b_b(); call c();

procedure seq_a_b_b_c:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_b_b(); call c();

procedure seq_c_a_b_c:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_a_b(); call c();

procedure seq_b_a_b_c:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_a_b(); call c();

procedure seq_a_a_b_c:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_a_b(); call c();

procedure seq_c_c_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_c_a(); call c();

procedure seq_b_c_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_c_a(); call c();

procedure seq_a_c_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_c_a(); call c();

procedure seq_c_b_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_b_a(); call c();

procedure seq_b_b_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_b_a(); call c();

procedure seq_a_b_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_b_a(); call c();

procedure seq_c_a_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_a_a(); call c();

procedure seq_b_a_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_a_a(); call c();

procedure seq_a_a_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_a_a(); call c();

procedure seq_c_c_c_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_c_c(); call b();

procedure seq_b_c_c_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_c_c(); call b();

procedure seq_a_c_c_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_c_c(); call b();

procedure seq_c_b_c_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_b_c(); call b();

procedure seq_b_b_c_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_b_c(); call b();

procedure seq_a_b_c_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_b_c(); call b();

procedure seq_c_a_c_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_a_c(); call b();

procedure seq_b_a_c_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_a_c(); call b();

procedure seq_a_a_c_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_a_c(); call b();

procedure seq_c_c_b_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_c_b(); call b();

procedure seq_b_c_b_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_c_b(); call b();

procedure seq_a_c_b_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_c_b(); call b();

procedure seq_c_b_b_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_b_b(); call b();

procedure seq_b_b_b_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_b_b(); call b();

procedure seq_a_b_b_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_b_b(); call b();

procedure seq_c_a_b_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_a_b(); call b();

procedure seq_b_a_b_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_a_b(); call b();

procedure seq_a_a_b_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_a_b(); call b();

procedure seq_c_c_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_c_a(); call b();

procedure seq_b_c_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_c_a(); call b();

procedure seq_a_c_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_c_a(); call b();

procedure seq_c_b_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_b_a(); call b();

procedure seq_b_b_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_b_a(); call b();

procedure seq_a_b_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_b_a(); call b();

procedure seq_c_a_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_a_a(); call b();

procedure seq_b_a_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_a_a(); call b();

procedure seq_a_a_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_a_a(); call b();

procedure seq_c_c_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_c_c(); call a();

procedure seq_b_c_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_c_c(); call a();

procedure seq_a_c_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_c_c(); call a();

procedure seq_c_b_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_b_c(); call a();

procedure seq_b_b_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_b_c(); call a();

procedure seq_a_b_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_b_c(); call a();

procedure seq_c_a_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_a_c(); call a();

procedure seq_b_a_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_a_c(); call a();

procedure seq_a_a_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_a_c(); call a();

procedure seq_c_c_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_c_b(); call a();

procedure seq_b_c_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_c_b(); call a();

procedure seq_a_c_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_c_b(); call a();

procedure seq_c_b_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_b_b(); call a();

procedure seq_b_b_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_b_b(); call a();

procedure seq_a_b_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_b_b(); call a();

procedure seq_c_a_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_a_b(); call a();

procedure seq_b_a_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_a_b(); call a();

procedure seq_a_a_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_a_b(); call a();

procedure seq_c_c_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_c_a(); call a();

procedure seq_b_c_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_c_a(); call a();

procedure seq_a_c_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_c_a(); call a();

procedure seq_c_b_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_b_a(); call a();

procedure seq_b_b_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_b_a(); call a();

procedure seq_a_b_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_b_a(); call a();

procedure seq_c_a_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c_a_a(); call a();

procedure seq_b_a_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b_a_a(); call a();

procedure seq_a_a_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a_a_a(); call a();
