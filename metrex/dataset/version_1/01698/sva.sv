// SVA for sky130_fd_sc_hdll__nand4
// Place inside the module or bind from TB. Focuses on functional and resolution checks.
// Uses immediate assertions for combinational logic, and concise coverage.

`ifndef SYNTHESIS
// Combinational functional correctness of internal nets
always @* begin
  // 2-input NANDs
  assert (nand0_out === ~(A & B)) else $error("nand0_out != ~(A&B)");
  assert (nand1_out === ~(C & D)) else $error("nand1_out != ~(C&D)");

  // Derived AND/OR
  assert (and0_out  ===  (A & B)) else $error("and0_out != A&B");
  assert (and1_out  ===  (C & D)) else $error("and1_out != C&D");
  assert (or0_out   === (and0_out | and1_out)) else $error("or0_out != and0|and1");

  // 2nd-level NAND and its NOT
  assert (nand2_out === ~(nand0_out & nand1_out)) else $error("nand2_out != ~(nand0&nand1)");
  assert (not0_out  === ~nand2_out) else $error("not0_out != ~nand2_out");

  // Consistency between two logic factorizations
  assert (or0_out   === (A & B) | (C & D)) else $error("or0_out != (A&B)|(C&D)");
  assert (nand2_out === or0_out) else $error("nand2_out != or0_out");
  assert (not0_out  === ~or0_out) else $error("not0_out != ~or0_out");

  // Y is driven by two buffers: not0_out and or0_out (multi-driver resolution)
  // If drivers agree and are known => Y must equal that value
  if (!$isunknown(not0_out) && !$isunknown(or0_out) && (not0_out === or0_out))
    assert (Y === or0_out) else $error("Y != agreed driver value");

  // If drivers are known and disagree => Y must be X
  if ((not0_out === 1'b0 && or0_out === 1'b1) || (not0_out === 1'b1 && or0_out === 1'b0))
    assert (Y === 1'bx) else $error("Y not X under driver contention");

  // If any driver is unknown => Y must be X
  if ($isunknown(not0_out) || $isunknown(or0_out))
    assert ($isunknown(Y)) else $error("Y not X when a driver is X/Z");
end

// Lightweight coverage
always @* begin
  // Input space corners
  cover ({A,B,C,D} == 4'b0000);
  cover ({A,B,C,D} == 4'b1111);
  cover ({A,B,C,D} == 4'b1100); // AB=1, CD=0
  cover ({A,B,C,D} == 4'b0011); // AB=0, CD=1

  // Internal function coverage
  cover (and0_out);          // A&B=1
  cover (and1_out);          // C&D=1
  cover (or0_out);           // (A&B)|(C&D)=1
  cover (not0_out);          // ~or0_out=1

  // Y resolution cases
  cover (!$isunknown(or0_out) && (or0_out === not0_out) && (Y === or0_out)); // agree -> Y known
  cover ((not0_out !== or0_out) && !$isunknown(not0_out) && !$isunknown(or0_out) && $isunknown(Y)); // contention -> X
  cover (($isunknown(not0_out) || $isunknown(or0_out)) && $isunknown(Y)); // unknown driver -> X
end
`endif