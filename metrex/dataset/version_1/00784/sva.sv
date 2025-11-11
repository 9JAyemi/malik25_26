// SVA for xor_and
// Concise, high-quality checks + essential coverage

module xor_and_sva
(
  input logic [3:0] vec1,
  input logic [3:0] vec2,
  input logic [3:0] out_xor,
  input logic       o4, o3, o2, o1, o0
);

  // Clockless sampling on any relevant signal change
  event ev;
  always @(vec1 or vec2 or out_xor or o4 or o3 or o2 or o1 or o0) -> ev;
  default clocking cb @(ev); endclocking

  // Functional correctness (##0 to avoid delta-cycle races)
  assert property ( ##0 (out_xor === (vec1 ^ vec2)) );
  assert property ( ##0 ({o3,o2,o1,o0} === out_xor) );
  // Note: o4 is the LSB of the bitwise AND due to width truncation
  assert property ( ##0 (o4 === (vec1[0] & vec2[0])) );

  // 4-state sanity: known inputs imply known outputs
  assert property ( (!$isunknown({vec1,vec2})) |-> ##0 (!$isunknown({out_xor,o4,o3,o2,o1,o0})) );

  // Outputs only change in response to input changes
  assert property ( $changed({out_xor,o4,o3,o2,o1,o0}) |-> $changed({vec1,vec2}) );

  // Minimal but meaningful coverage
  cover property ( $changed(out_xor[0]) );
  cover property ( $changed(out_xor[1]) );
  cover property ( $changed(out_xor[2]) );
  cover property ( $changed(out_xor[3]) );

  cover property ( out_xor == 4'h0 ); // vec1 == vec2
  cover property ( out_xor == 4'hF ); // vec2 == ~vec1

  cover property ( o4 );              // exercise AND LSB = 1
  cover property ( !o4 );
  cover property ( |((vec1 & vec2)[3:1]) ); // exercise truncated upper AND bits
endmodule

bind xor_and xor_and_sva sva_i (.*);