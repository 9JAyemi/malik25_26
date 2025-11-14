// SVA for sparc_exu_aluor32
// Bind this into the DUT. Provide a sampling clock/reset from your TB.
module sparc_exu_aluor32_sva (input logic clk, input logic rst_n);
  // This module is bound into sparc_exu_aluor32; it can reference its internal nets by name.

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Helpers to reason about 4-state determinism
  function automatic bit any_one (input logic [31:0] v);
    any_one = 0;
    foreach (v[i]) if (v[i] === 1'b1) begin any_one = 1; break; end
  endfunction
  function automatic bit all_zero (input logic [31:0] v);
    all_zero = 1;
    foreach (v[i]) if (v[i] !== 1'b0) begin all_zero = 0; break; end
  endfunction

  // Structural/netlist consistency
  a_nor1_1 : assert property (nor1_1  === ~(in[1]  | in[0]));
  a_nor1_2 : assert property (nor1_2  === ~(in[3]  | in[2]));
  a_nor1_3 : assert property (nor1_3  === ~(in[5]  | in[4]));
  a_nor1_4 : assert property (nor1_4  === ~(in[7]  | in[6]));
  a_nor1_5 : assert property (nor1_5  === ~(in[9]  | in[8]));
  a_nor1_6 : assert property (nor1_6  === ~(in[11] | in[10]));
  a_nor1_7 : assert property (nor1_7  === ~(in[13] | in[12]));
  a_nor1_8 : assert property (nor1_8  === ~(in[15] | in[14]));
  a_nor1_9 : assert property (nor1_9  === ~(in[17] | in[16]));
  a_nor1_10: assert property (nor1_10 === ~(in[19] | in[18]));
  a_nor1_11: assert property (nor1_11 === ~(in[21] | in[20]));
  a_nor1_12: assert property (nor1_12 === ~(in[23] | in[22]));
  a_nor1_13: assert property (nor1_13 === ~(in[25] | in[24]));
  a_nor1_14: assert property (nor1_14 === ~(in[27] | in[26]));
  a_nor1_15: assert property (nor1_15 === ~(in[29] | in[28]));
  a_nor1_16: assert property (nor1_16 === ~(in[31] | in[30]));

  a_nand2_1: assert property (nand2_1 === ~(nor1_1  & nor1_2  & nor1_3  & nor1_4));
  a_nand2_2: assert property (nand2_2 === ~(nor1_5  & nor1_6  & nor1_7  & nor1_8));
  a_nand2_3: assert property (nand2_3 === ~(nor1_9  & nor1_10 & nor1_11 & nor1_12));
  a_nand2_4: assert property (nand2_4 === ~(nor1_13 & nor1_14 & nor1_15 & nor1_16));

  a_inv3_1 : assert property (inv3_1 === ~nand2_1);
  a_inv3_2 : assert property (inv3_2 === ~nand2_2);
  a_inv3_3 : assert property (inv3_3 === ~nand2_3);
  a_inv3_4 : assert property (inv3_4 === ~nand2_4);

  a_out_tree: assert property (out === ~(inv3_1 & inv3_2 & inv3_3 & inv3_4));

  // Functional correctness and X-handling
  a_no_x_out_when_no_x_in: assert property (!$isunknown(in) |-> !$isunknown(out));
  a_or_value_when_no_x   : assert property (!$isunknown(in) |-> (out == (|in)));
  a_out_1_if_any_known_1 : assert property (any_one(in)  |-> (out == 1'b1));
  a_out_0_if_all_known_0 : assert property (all_zero(in) |-> (out == 1'b0));

  // Functional coverage
  c_all_zero: cover property (all_zero(in) && (out == 1'b0));
  genvar i;
  generate
    for (i = 0; i < 32; i++) begin : gen_onehot_cov
      c_onehot: cover property ((in == (32'h1 << i)) && (out == 1'b1));
    end
  endgenerate
endmodule

// Example bind (hook clk/rst from your environment):
// bind sparc_exu_aluor32 sparc_exu_aluor32_sva u_sva (.clk(clk), .rst_n(rst_n));