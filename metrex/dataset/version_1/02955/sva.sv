// SVA for xor_splitter and submodules (concise, full functional checks + key coverage)
//
// Uses $global_clock for combinational sampling. Add to your sim if not already enabled.

bind xor_splitter
module xor_splitter_sva;
  default clocking cb @(posedge $global_clock); endclocking

  // End-to-end functional equivalence
  assert property (##0 out_xor == ((a ? in[15:8] : in[7:0]) ^ (b ? in[15:8] : in[7:0])));

  // Internal wiring consistency
  assert property (##0 out_xor == (upper_byte ^ lower_byte));

  // No X on output when inputs are known
  assert property (##0 (!$isunknown({in,a,b})) |-> !$isunknown(out_xor));

  // Key scenario coverage
  cover property (##0 {a,b} == 2'b00);
  cover property (##0 {a,b} == 2'b01);
  cover property (##0 {a,b} == 2'b10);
  cover property (##0 {a,b} == 2'b11);
  cover property (##0 (in[15:8] == in[7:0]) && (out_xor == 8'h00));
  cover property (##0 (in[15:8] != in[7:0]) && (out_xor != 8'h00));
  cover property (##0 out_xor == 8'hFF);
endmodule


bind splitter16
module splitter16_sva;
  default clocking cb @(posedge $global_clock); endclocking

  // Splitter correctness
  assert property (##0 upper == (a ? in[15:8] : in[7:0]));
  assert property (##0 lower == (b ? in[15:8] : in[7:0]));

  // When selects are equal, halves must match
  assert property (##0 (a == b) |-> (upper == lower));

  // No X on outputs when inputs are known
  assert property (##0 (!$isunknown({in,a,b})) |-> !$isunknown({upper,lower}));

  // Coverage of both selection paths per output
  cover property (##0 (a == 0) && (upper == in[7:0]));
  cover property (##0 (a == 1) && (upper == in[15:8]));
  cover property (##0 (b == 0) && (lower == in[7:0]));
  cover property (##0 (b == 1) && (lower == in[15:8]));
endmodule


bind xor_gate
module xor_gate_sva;
  default clocking cb @(posedge $global_clock); endclocking

  // XOR correctness
  assert property (##0 out == (in1 ^ in2));

  // No X on output when inputs are known
  assert property (##0 (!$isunknown({in1,in2})) |-> !$isunknown(out));

  // Useful XOR coverage
  cover property (##0 out == 8'h00);
  cover property (##0 out == 8'hFF);
endmodule