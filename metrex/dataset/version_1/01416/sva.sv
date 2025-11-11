// SVA checker for bitwise_operations
module bitwise_operations_sva #(parameter WIDTH=3)
(
  input  logic                     clk,
  input  logic                     rst_n,
  input  logic [WIDTH-1:0]         a,
  input  logic [WIDTH-1:0]         b,
  input  logic [WIDTH-1:0]         out_and,
  input  logic [WIDTH-1:0]         out_xor,
  input  logic [WIDTH-1:0]         out_nand
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // No X/Z on outputs whenever inputs are known
  ap_no_xz: assert property (!$isunknown({a,b}) |-> !$isunknown({out_and,out_xor,out_nand}));

  // Functional correctness
  ap_and    : assert property (out_and  == (a & b));
  ap_xor    : assert property (out_xor  == (a ^ b));
  // Intentionally checks bitwise NAND (exposes bug if logical ! is used in DUT)
  ap_nand   : assert property (out_nand == ~(a & b));

  // Cross-consistency checks
  ap_and_nand_compl: assert property (~out_nand == out_and);
  ap_union_matches : assert property ((out_and | out_xor) == (a | b));
  ap_xor_alt_form  : assert property (out_xor == (a | b) & ~(a & b));

  // Lightweight full input space coverage (all 64 combinations for WIDTH=3)
  genvar i,j;
  generate
    for (i = 0; i < (1<<WIDTH); i++) begin : COV_A
      for (j = 0; j < (1<<WIDTH); j++) begin : COV_B
        cp_all_inputs: cover property (a == i[WIDTH-1:0] && b == j[WIDTH-1:0]);
      end
    end
  endgenerate

endmodule

// Example bind (provide clk,rst_n from TB/env):
// bind bitwise_operations bitwise_operations_sva #(.WIDTH(3))
//   bitwise_operations_sva_i (.clk(tb_clk), .rst_n(tb_rst_n), .a(a), .b(b), .out_and(out_and), .out_xor(out_xor), .out_nand(out_nand));