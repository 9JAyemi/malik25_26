// SVA for alu. Bind this to the DUT. Assumes an external clk/rst_n for sampling.

module alu_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [31:0] a_in,
  input  logic [31:0] b_in,
  input  logic [ 3:0] alu_function,
  input  logic [31:0] c_alu,
  // internal DUT nets (connected via bind)
  input  logic [32:0] aa,
  input  logic [32:0] bb,
  input  logic [32:0] sum,
  input  logic        do_add,
  input  logic        sign_ext
);

  default clocking cb @(posedge clk); endclocking

  // Local expectations
  let exp_do_add    = (alu_function == 4'b0001);
  let exp_sign_ext  = !(alu_function == 4'b0010);
  let exp_aa        = { (a_in[31] & sign_ext), a_in };
  let exp_bb        = { (b_in[31] & sign_ext), b_in };
  let exp_sum       = do_add ? (aa + bb) : (aa - bb);
  let exp_c =
      (alu_function == 4'b0001) ? sum[31:0] :
      (alu_function == 4'b0010) ? {31'b0, sum[32]} :
      (alu_function == 4'b0100) ? (a_in | b_in)    :
      (alu_function == 4'b0101) ? (a_in & b_in)    :
      (alu_function == 4'b0110) ? (a_in ^ b_in)    :
      (alu_function == 4'b0111) ? ~(a_in | b_in)   :
                                  32'b0;

  // Structural/internal checks
  a_do_add    : assert property (disable iff (!rst_n) do_add   == exp_do_add);
  a_sign_ext  : assert property (disable iff (!rst_n) sign_ext == exp_sign_ext);
  a_aa        : assert property (disable iff (!rst_n) aa == exp_aa);
  a_bb        : assert property (disable iff (!rst_n) bb == exp_bb);
  a_sum_mux   : assert property (disable iff (!rst_n) sum == exp_sum);

  // Output functional check (full behavior)
  a_c_ref     : assert property (disable iff (!rst_n) c_alu == exp_c);

  // Decode/output per-op (redundant with a_c_ref but pinpoints fails)
  a_add       : assert property (disable iff (!rst_n)
                                 (alu_function==4'b0001) |-> (c_alu == sum[31:0]));
  a_slt       : assert property (disable iff (!rst_n)
                                 (alu_function==4'b0010) |-> (c_alu == {31'b0,sum[32]}));
  a_or        : assert property (disable iff (!rst_n)
                                 (alu_function==4'b0100) |-> (c_alu == (a_in | b_in)));
  a_and       : assert property (disable iff (!rst_n)
                                 (alu_function==4'b0101) |-> (c_alu == (a_in & b_in)));
  a_xor       : assert property (disable iff (!rst_n)
                                 (alu_function==4'b0110) |-> (c_alu == (a_in ^ b_in)));
  a_nor       : assert property (disable iff (!rst_n)
                                 (alu_function==4'b0111) |-> (c_alu == ~(a_in | b_in)));
  a_default   : assert property (disable iff (!rst_n)
                                 (!(alu_function inside {4'b0001,4'b0010,4'b0100,4'b0101,4'b0110,4'b0111}))
                                 |-> (c_alu == 32'b0));

  // Basic X/Z hygiene (optional but useful)
  a_no_x_ctrl : assert property (disable iff (!rst_n) !$isunknown(alu_function));

  // Coverage
  c_add       : cover property (disable iff (!rst_n) alu_function==4'b0001);
  c_slt       : cover property (disable iff (!rst_n) alu_function==4'b0010);
  c_or        : cover property (disable iff (!rst_n) alu_function==4'b0100);
  c_and       : cover property (disable iff (!rst_n) alu_function==4'b0101);
  c_xor       : cover property (disable iff (!rst_n) alu_function==4'b0110);
  c_nor       : cover property (disable iff (!rst_n) alu_function==4'b0111);
  c_default   : cover property (disable iff (!rst_n)
                                !(alu_function inside {4'b0001,4'b0010,4'b0100,4'b0101,4'b0110,4'b0111}));

  c_do_add0   : cover property (disable iff (!rst_n) do_add==1'b0);
  c_do_add1   : cover property (disable iff (!rst_n) do_add==1'b1);
  c_se0       : cover property (disable iff (!rst_n) sign_ext==1'b0);
  c_se1       : cover property (disable iff (!rst_n) sign_ext==1'b1);

  // Compare outcome coverage
  c_slt_true  : cover property (disable iff (!rst_n)
                                alu_function==4'b0010 && c_alu==32'h0000_0001);
  c_slt_false : cover property (disable iff (!rst_n)
                                alu_function==4'b0010 && c_alu==32'h0000_0000);

  // Extension bit activity
  c_aa32_0    : cover property (disable iff (!rst_n) aa[32]==1'b0);
  c_aa32_1    : cover property (disable iff (!rst_n) aa[32]==1'b1);
  c_bb32_0    : cover property (disable iff (!rst_n) bb[32]==1'b0);
  c_bb32_1    : cover property (disable iff (!rst_n) bb[32]==1'b1);

endmodule

// Bind example (connect clk/rst_n from your TB)
bind alu alu_sva u_alu_sva (
  .clk         (clk),
  .rst_n       (rst_n),
  .a_in        (a_in),
  .b_in        (b_in),
  .alu_function(alu_function),
  .c_alu       (c_alu),
  .aa          (aa),
  .bb          (bb),
  .sum         (sum),
  .do_add      (do_add),
  .sign_ext    (sign_ext)
);