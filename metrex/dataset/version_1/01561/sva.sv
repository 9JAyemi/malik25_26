// SystemVerilog Assertions for carry_select_adder and sub-blocks.
// Bind these in your testbench; they include functional checks and concise coverage.

module csa_sva;
  // simple sampling clock for combinational DUT
  bit clk = 0; always #1 clk = ~clk;
  default clocking @(posedge clk); endclocking

  // zero-extended references
  wire [32:0] add_cin     = {1'b0, a} + {1'b0, b} + cin;
  wire [32:0] add_not_cin = {1'b0, a} + {1'b0, b} + ~cin;

  // Golden functionality (33-bit equivalence)
  assert property (1 |-> {cout, sum} == add_cin);

  // Internal RCA correctness vs arithmetic truth
  assert property (1 |-> ripple_carry_out_0[30:0] == add_cin[30:0]
                        && ripple_carry_out_0[31] == add_cin[32]);
  assert property (1 |-> ripple_carry_out_1[30:0] == add_not_cin[30:0]
                        && ripple_carry_out_1[31] == add_not_cin[32]);

  // Structural checks
  assert property (1 |-> sum == (cin ? ripple_carry_out_1 : ripple_carry_out_0));
  assert property (1 |-> cout == (cin ? ripple_carry_out_1[31] : ripple_carry_out_0[31]));

  // X checks
  assert property (1 |-> !$isunknown({a,b,cin}));
  assert property (1 |-> !$isunknown({sum,cout}));

  // Coverage
  cover property (cin == 0);
  cover property (cin == 1);
  cover property (add_cin[32] == 1); // overflow case
  cover property (ripple_carry_out_0 != ripple_carry_out_1); // mux relevance
  // cases where selected carry differs from the other precompute (exposes bad OR)
  cover property ( cin && (ripple_carry_out_1[31]==0) && (ripple_carry_out_0[31]==1));
  cover property (!cin && (ripple_carry_out_1[31]==1) && (ripple_carry_out_0[31]==0));
endmodule

bind carry_select_adder csa_sva csa_sva_i();

module rca32_sva;
  bit clk = 0; always #1 clk = ~clk;
  default clocking @(posedge clk); endclocking

  wire [32:0] add = {1'b0, a} + {1'b0, b} + cin;

  // rca32 mapping: cout[30:0]=sum[30:0], cout[31]=carry_out
  assert property (1 |-> cout[30:0] == add[30:0] && cout[31] == add[32]);

  assert property (1 |-> !$isunknown({a,b,cin}));
  assert property (1 |-> !$isunknown(cout));
endmodule

bind rca32 rca32_sva rca32_sva_i();

module full_adder_sva;
  bit clk = 0; always #1 clk = ~clk;
  default clocking @(posedge clk); endclocking

  wire [1:0] add = {1'b0, a} + {1'b0, b} + cin;
  assert property (1 |-> {cout, sum} == add);
endmodule

bind full_adder full_adder_sva fa_sva_i();