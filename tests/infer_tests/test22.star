procedure a:
  {@s=1} (@s) {false||@s=1||@s=2}
  {emp*@s!=1} () {emp}
procedure c:
  {emp} () {emp}
procedure b:
  {@s=2} (@s) {false||@s=1||@s=3}
  {emp*@s!=2} () {emp}

procedure seq_:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
?

procedure seq_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call a();

procedure seq_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call c();

procedure seq_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call b();

procedure seq_a_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call a(); call a();

procedure seq_c_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call c(); call a();

procedure seq_b_a:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=1||@s=2||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call b(); call a();

procedure seq_a_c:
  // {@s=1} (@s) {false||@s=1||@s=2}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call a(); call c();

procedure seq_c_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=2}
  // {@s=3} (@s) {false||@s=3}
? call c(); call c();

procedure seq_b_c:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call b(); call c();

procedure seq_a_b:
  // {@s=1} (@s) {false||@s=1||@s=3}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call a(); call b();

procedure seq_c_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call c(); call b();

procedure seq_b_b:
  // {@s=1} (@s) {false||@s=1}
  // {@s=2} (@s) {false||@s=1||@s=3}
  // {@s=3} (@s) {false||@s=3}
? call b(); call b();
