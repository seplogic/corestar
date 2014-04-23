procedure a:
  {@s=1} (@s) {false||@s=1||@s=2}
  {emp*@s!=1} () {emp}
procedure b:
  {@s=2} (@s) {false||@s=1||@s=3}
  {emp*@s!=2} () {emp}
procedure c:
  {emp} () {emp}

procedure seq_:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
?

procedure seq_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_(); call a();

procedure seq_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_(); call b();

procedure seq_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_(); call c();

procedure seq_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a(); call a();

procedure seq_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b(); call a();

procedure seq_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c(); call a();

procedure seq_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_a(); call b();

procedure seq_b_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b(); call b();

procedure seq_c_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_c(); call b();

procedure seq_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_a(); call c();

procedure seq_b_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call seq_b(); call c();

procedure seq_c_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call seq_c(); call c();
