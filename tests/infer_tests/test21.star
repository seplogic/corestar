procedure c:
  {emp} () {emp}
procedure b:
  {$gs=2} ($gs) {false||$gs=1||$gs=3}
  {emp*$gs!=2} () {emp}
procedure a:
  {$gs=1} ($gs) {false||$gs=1||$gs=2}
  {emp*$gs!=1} () {emp}

procedure seq_:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
?

procedure seq_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_(); call c();

procedure seq_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_(); call b();

procedure seq_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_(); call a();

procedure seq_c_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c(); call c();

procedure seq_b_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b(); call c();

procedure seq_a_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a(); call c();

procedure seq_c_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c(); call b();

procedure seq_b_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b(); call b();

procedure seq_a_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a(); call b();

procedure seq_c_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c(); call a();

procedure seq_b_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b(); call a();

procedure seq_a_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a(); call a();

procedure seq_c_c_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_c(); call c();

procedure seq_b_c_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_c(); call c();

procedure seq_a_c_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_c(); call c();

procedure seq_c_b_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_b(); call c();

procedure seq_b_b_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_b(); call c();

procedure seq_a_b_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_b(); call c();

procedure seq_c_a_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_a(); call c();

procedure seq_b_a_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_a(); call c();

procedure seq_a_a_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_a(); call c();

procedure seq_c_c_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_c(); call b();

procedure seq_b_c_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_c(); call b();

procedure seq_a_c_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_c(); call b();

procedure seq_c_b_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_b(); call b();

procedure seq_b_b_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_b(); call b();

procedure seq_a_b_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_b(); call b();

procedure seq_c_a_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_a(); call b();

procedure seq_b_a_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_a(); call b();

procedure seq_a_a_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_a(); call b();

procedure seq_c_c_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_c(); call a();

procedure seq_b_c_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_c(); call a();

procedure seq_a_c_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_c(); call a();

procedure seq_c_b_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_b(); call a();

procedure seq_b_b_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_b(); call a();

procedure seq_a_b_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_b(); call a();

procedure seq_c_a_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_a(); call a();

procedure seq_b_a_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_a(); call a();

procedure seq_a_a_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_a(); call a();

procedure seq_c_c_c_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_c_c(); call c();

procedure seq_b_c_c_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_c_c(); call c();

procedure seq_a_c_c_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_c_c(); call c();

procedure seq_c_b_c_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_b_c(); call c();

procedure seq_b_b_c_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_b_c(); call c();

procedure seq_a_b_c_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_b_c(); call c();

procedure seq_c_a_c_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_a_c(); call c();

procedure seq_b_a_c_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_a_c(); call c();

procedure seq_a_a_c_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_a_c(); call c();

procedure seq_c_c_b_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_c_b(); call c();

procedure seq_b_c_b_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_c_b(); call c();

procedure seq_a_c_b_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_c_b(); call c();

procedure seq_c_b_b_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_b_b(); call c();

procedure seq_b_b_b_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_b_b(); call c();

procedure seq_a_b_b_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_b_b(); call c();

procedure seq_c_a_b_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_a_b(); call c();

procedure seq_b_a_b_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_a_b(); call c();

procedure seq_a_a_b_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_a_b(); call c();

procedure seq_c_c_a_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_c_a(); call c();

procedure seq_b_c_a_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_c_a(); call c();

procedure seq_a_c_a_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_c_a(); call c();

procedure seq_c_b_a_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_b_a(); call c();

procedure seq_b_b_a_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_b_a(); call c();

procedure seq_a_b_a_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_b_a(); call c();

procedure seq_c_a_a_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_a_a(); call c();

procedure seq_b_a_a_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_a_a(); call c();

procedure seq_a_a_a_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_a_a(); call c();

procedure seq_c_c_c_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_c_c(); call b();

procedure seq_b_c_c_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_c_c(); call b();

procedure seq_a_c_c_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_c_c(); call b();

procedure seq_c_b_c_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_b_c(); call b();

procedure seq_b_b_c_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_b_c(); call b();

procedure seq_a_b_c_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_b_c(); call b();

procedure seq_c_a_c_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_a_c(); call b();

procedure seq_b_a_c_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_a_c(); call b();

procedure seq_a_a_c_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_a_c(); call b();

procedure seq_c_c_b_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_c_b(); call b();

procedure seq_b_c_b_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_c_b(); call b();

procedure seq_a_c_b_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_c_b(); call b();

procedure seq_c_b_b_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_b_b(); call b();

procedure seq_b_b_b_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_b_b(); call b();

procedure seq_a_b_b_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_b_b(); call b();

procedure seq_c_a_b_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_a_b(); call b();

procedure seq_b_a_b_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_a_b(); call b();

procedure seq_a_a_b_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_a_b(); call b();

procedure seq_c_c_a_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_c_a(); call b();

procedure seq_b_c_a_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_c_a(); call b();

procedure seq_a_c_a_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_c_a(); call b();

procedure seq_c_b_a_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_b_a(); call b();

procedure seq_b_b_a_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_b_a(); call b();

procedure seq_a_b_a_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_b_a(); call b();

procedure seq_c_a_a_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_a_a(); call b();

procedure seq_b_a_a_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_a_a(); call b();

procedure seq_a_a_a_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_a_a(); call b();

procedure seq_c_c_c_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_c_c(); call a();

procedure seq_b_c_c_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_c_c(); call a();

procedure seq_a_c_c_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_c_c(); call a();

procedure seq_c_b_c_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_b_c(); call a();

procedure seq_b_b_c_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_b_c(); call a();

procedure seq_a_b_c_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_b_c(); call a();

procedure seq_c_a_c_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_a_c(); call a();

procedure seq_b_a_c_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_a_c(); call a();

procedure seq_a_a_c_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_a_c(); call a();

procedure seq_c_c_b_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_c_b(); call a();

procedure seq_b_c_b_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_c_b(); call a();

procedure seq_a_c_b_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_c_b(); call a();

procedure seq_c_b_b_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_b_b(); call a();

procedure seq_b_b_b_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_b_b(); call a();

procedure seq_a_b_b_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_b_b(); call a();

procedure seq_c_a_b_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_a_b(); call a();

procedure seq_b_a_b_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_a_b(); call a();

procedure seq_a_a_b_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_a_b(); call a();

procedure seq_c_c_a_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_c_a(); call a();

procedure seq_b_c_a_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_c_a(); call a();

procedure seq_a_c_a_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_c_a(); call a();

procedure seq_c_b_a_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_b_a(); call a();

procedure seq_b_b_a_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_b_a(); call a();

procedure seq_a_b_a_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_b_a(); call a();

procedure seq_c_a_a_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_c_a_a(); call a();

procedure seq_b_a_a_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_b_a_a(); call a();

procedure seq_a_a_a_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call seq_a_a_a(); call a();
