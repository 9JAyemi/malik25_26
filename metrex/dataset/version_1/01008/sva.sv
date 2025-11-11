// SVA for macc_simple_ena
module macc_simple_ena_sva (
  input logic        clk,
  input logic        ena,
  input logic [7:0]  A,
  input logic [7:0]  B,
  input logic [15:0] Z
);
  default clocking @(posedge clk); endclocking
  default disable iff ($initstate);

  // Functional correctness
  assert property (ena |=> Z == $past(Z) + $past(A)*$past(B));
  assert property (!ena |=> Z == $past(Z));
  assert property ((Z != $past(Z)) |-> $past(ena));

  // X-safety
  assert property (!$isunknown({ena,A,B}));
  assert property (ena && !$isunknown($past({Z,A,B})) |=> !$isunknown(Z));

  // Coverage
  cover property (ena && (A!=0) && (B!=0) ##1 Z == $past(Z) + $past(A)*$past(B)); // non-trivial update
  cover property (!ena ##1 Z == $past(Z));                                        // hold
  cover property (ena && (A!=0) && (B!=0) ##1 (Z < $past(Z)));                    // 16-bit wraparound

endmodule

bind macc_simple_ena macc_simple_ena_sva sva_i (
  .clk(clk), .ena(ena), .A(A), .B(B), .Z(Z)
);