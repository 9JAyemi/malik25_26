// SVA checker for oh_mux4
module oh_mux4_sva #(parameter DW=1) (
  input  logic              clk,
  input  logic              rst_n,
  input  logic              sel3, sel2, sel1, sel0,
  input  logic [DW-1:0]     in3, in2, in1, in0,
  input  logic [DW-1:0]     out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  wire [3:0] sel = {sel3,sel2,sel1,sel0};

  // At most one select asserted (0-hot or 1-hot)
  a_onehot0: assert property ($onehot0(sel))
    else $error("oh_mux4: selects not onehot0: %b", sel);

  // Functional equivalence to masked-OR; gated to avoid X-propagation noise
  a_equiv: assert property (
    !$isunknown({sel,in0,in1,in2,in3,out})
    |-> out == ((sel0 ? in0 : '0) |
                (sel1 ? in1 : '0) |
                (sel2 ? in2 : '0) |
                (sel3 ? in3 : '0))
  ) else $error("oh_mux4: out mismatch");

  // If selects and inputs are known, output must be known
  a_no_x_out: assert property (
    !$isunknown({sel,in0,in1,in2,in3}) |-> !$isunknown(out)
  ) else $error("oh_mux4: X/Z on out with known inputs/selects");

  // Path coverage for each select and the none-selected case
  c_sel0: cover property ($onehot(sel) && sel0 && out == in0);
  c_sel1: cover property ($onehot(sel) && sel1 && out == in1);
  c_sel2: cover property ($onehot(sel) && sel2 && out == in2);
  c_sel3: cover property ($onehot(sel) && sel3 && out == in3);
  c_none: cover property (~(|sel) && out == '0);

  // Illegal multi-hot coverage (should be prevented by a_onehot0)
  c_illegal_multi: cover property ($countones(sel) >= 2);

endmodule

// Bind (provide clk/rst_n from your environment)
bind oh_mux4 oh_mux4_sva #(.DW(DW)) oh_mux4_sva_i (
  .clk(clk), .rst_n(rst_n),
  .sel3(sel3), .sel2(sel2), .sel1(sel1), .sel0(sel0),
  .in3(in3), .in2(in2), .in1(in1), .in0(in0),
  .out(out)
);