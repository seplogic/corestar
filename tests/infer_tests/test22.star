procedure a:
  {$gs=1} ($gs) {false||$gs=1||$gs=2}
  {emp*$gs!=1} () {emp}
procedure c:
  {emp} () {emp}
procedure b:
  {$gs=2} ($gs) {false||$gs=1||$gs=3}
  {emp*$gs!=2} () {emp}

procedure seq_:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
?

procedure seq_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call a();

procedure seq_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call c();

procedure seq_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call b();

procedure seq_a_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call a(); call a();

procedure seq_c_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call c(); call a();

procedure seq_b_a:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=1||$gs=2||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call b(); call a();

procedure seq_a_c:
  // {$gs=1} ($gs) {false||$gs=1||$gs=2}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call a(); call c();

procedure seq_c_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=2}
  // {$gs=3} ($gs) {false||$gs=3}
? call c(); call c();

procedure seq_b_c:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call b(); call c();

procedure seq_a_b:
  // {$gs=1} ($gs) {false||$gs=1||$gs=3}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call a(); call b();

procedure seq_c_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call c(); call b();

procedure seq_b_b:
  // {$gs=1} ($gs) {false||$gs=1}
  // {$gs=2} ($gs) {false||$gs=1||$gs=3}
  // {$gs=3} ($gs) {false||$gs=3}
? call b(); call b();
