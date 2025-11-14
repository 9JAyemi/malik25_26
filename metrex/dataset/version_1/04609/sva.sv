// SVA for top_module
// Bind into the DUT; checks are purely combinational (@(*))
module top_module_sva (
  input  logic [2:0] a,
  input  logic [2:0] b,
  input  logic [2:0] out_or_bitwise,
  input  logic       out_or_logical,
  input  logic [5:0] out_not,
  input  logic [2:0] out_and,
  input  logic [2:0] not_a,
  input  logic [2:0] not_b
);
  default clocking cb @(*); endclocking

  // Internal module correctness
  a_and:         assert property (out_and        === (a & b));
  a_not_a:       assert property (not_a          === ~a);
  a_not_b:       assert property (not_b          === ~b);

  // Top-level outputs correctness
  a_or_bitwise:  assert property (out_or_bitwise === (a | b));
  a_or_log_def:  assert property (out_or_logical === ((a != 3'b000) || (b != 3'b000)));
  a_or_log_cons: assert property (out_or_logical === (|out_or_bitwise));
  a_out_not:     assert property (out_not        === {~b, ~a});

  // Useful logical relationships
  a_imp_zero1:   assert property ((out_or_bitwise === 3'b000) |-> (out_or_logical === 1'b0));
  a_imp_zero2:   assert property ((out_or_logical === 1'b0)   |-> (out_or_bitwise === 3'b000));

  // Coverage
  c_log0:        cover  property (out_or_logical === 1'b0);
  c_log1:        cover  property (out_or_logical === 1'b1);
  c_a0b0:        cover  property ((a == 3'b000) && (b == 3'b000));
  c_a_only:      cover  property ((a != 3'b000) && (b == 3'b000));
  c_b_only:      cover  property ((a == 3'b000) && (b != 3'b000));
  c_both_nz:     cover  property ((a != 3'b000) && (b != 3'b000));
  c_or_001:      cover  property (out_or_bitwise == 3'b001);
  c_or_010:      cover  property (out_or_bitwise == 3'b010);
  c_or_100:      cover  property (out_or_bitwise == 3'b100);
  c_or_111:      cover  property (out_or_bitwise == 3'b111);
  c_not_all1:    cover  property (out_not == 6'b111111);
  c_not_all0:    cover  property (out_not == 6'b000000);
  c_rose_log:    cover  property ($rose(out_or_logical));
  c_fell_log:    cover  property ($fell(out_or_logical));
endmodule

bind top_module top_module_sva sva_top (
  .a(a),
  .b(b),
  .out_or_bitwise(out_or_bitwise),
  .out_or_logical(out_or_logical),
  .out_not(out_not),
  .out_and(out_and),
  .not_a(not_a),
  .not_b(not_b)
);