// SVA for and_gate and its leaf gates. Bind these to the DUT; no DUT edits needed.

module and_gate_sva(input logic a,b,c, out, input logic and_output);
  // Structural correctness
  assert property (@(*) and_output === (a & b & c));
  assert property (@(*) out        === (and_output | c));

  // Simplified equivalence (absorption): out must always equal c
  assert property (@(*) out === c);

  // Structural invariant: if and_output is 1 then c must be 1
  assert property (@(*) (and_output === 1'b1) |-> (c === 1'b1));

  // Reachability/functional coverage on inputs
  cover property (@(*) {a,b,c} == 3'b000);
  cover property (@(*) {a,b,c} == 3'b001);
  cover property (@(*) {a,b,c} == 3'b010);
  cover property (@(*) {a,b,c} == 3'b011);
  cover property (@(*) {a,b,c} == 3'b100);
  cover property (@(*) {a,b,c} == 3'b101);
  cover property (@(*) {a,b,c} == 3'b110);
  cover property (@(*) {a,b,c} == 3'b111);

  // OR2 input space reachable pairs (and_output,c)
  cover property (@(*) {and_output,c} == 2'b00);
  cover property (@(*) {and_output,c} == 2'b01);
  cover property (@(*) {and_output,c} == 2'b11);

  // Output edges (since out == c, these mirror c’s edges)
  cover property (@(posedge out) 1'b1);
  cover property (@(negedge out) 1'b1);
endmodule

module and3_gate_sva(input logic a,b,c,out);
  // Truth function
  assert property (@(*) out === (a & b & c));

  // Full truth-table coverage
  cover property (@(*) {a,b,c,out} == 4'b0000);
  cover property (@(*) {a,b,c,out} == 4'b0001);
  cover property (@(*) {a,b,c,out} == 4'b0010);
  cover property (@(*) {a,b,c,out} == 4'b0011);
  cover property (@(*) {a,b,c,out} == 4'b0100);
  cover property (@(*) {a,b,c,out} == 4'b0101);
  cover property (@(*) {a,b,c,out} == 4'b0110);
  cover property (@(*) {a,b,c,out} == 4'b0111);
  cover property (@(*) {a,b,c,out} == 4'b1000);
  cover property (@(*) {a,b,c,out} == 4'b1001);
  cover property (@(*) {a,b,c,out} == 4'b1010);
  cover property (@(*) {a,b,c,out} == 4'b1011);
  cover property (@(*) {a,b,c,out} == 4'b1100);
  cover property (@(*) {a,b,c,out} == 4'b1101);
  cover property (@(*) {a,b,c,out} == 4'b1110);
  cover property (@(*) {a,b,c,out} == 4'b1111);
endmodule

module or2_gate_sva(input logic a,b,out);
  // Truth function
  assert property (@(*) out === (a | b));

  // Full truth-table coverage
  cover property (@(*) {a,b,out} == 3'b000);
  cover property (@(*) {a,b,out} == 3'b001);
  cover property (@(*) {a,b,out} == 3'b010);
  cover property (@(*) {a,b,out} == 3'b011);
  cover property (@(*) {a,b,out} == 3'b100);
  cover property (@(*) {a,b,out} == 3'b101);
  cover property (@(*) {a,b,out} == 3'b110);
  cover property (@(*) {a,b,out} == 3'b111);
endmodule

bind and_gate   and_gate_sva   and_gate_sva_i   (.*);
bind and3_gate  and3_gate_sva  and3_gate_sva_i  (.*);
bind or2_gate   or2_gate_sva   or2_gate_sva_i   (.*);