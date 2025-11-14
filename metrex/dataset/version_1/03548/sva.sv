// SVA for adder_subtractor. Bind this to the DUT and drive clk/rst_n from TB.

module adder_subtractor_sva #(parameter W=4)
(
  input logic               clk,
  input logic               rst_n,   // active-low reset for disable iff
  input logic [W-1:0]       A,
  input logic [W-1:0]       B,
  input logic               mode,
  input logic [W-1:0]       result
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Extended arithmetic for overflow/borrow introspection and explicit truncation
  logic [W:0] add_ext, sub_ext;
  assign add_ext = {1'b0, A} + {1'b0, B};
  assign sub_ext = {1'b0, A} - {1'b0, B};

  // Functional correctness (same-cycle, combinational)
  assert property (!$isunknown({A,B,mode}) |-> result == (mode ? sub_ext[W-1:0] : add_ext[W-1:0]));

  // Combinational stability: if inputs don’t change, output doesn’t change
  assert property ($stable({A,B,mode}) |-> $stable(result));

  // No X on output when inputs are known
  assert property (!$isunknown({A,B,mode}) |-> !$isunknown(result));

  // Functional coverage
  cover property (mode==0);                            // add mode seen
  cover property (mode==1);                            // sub mode seen
  cover property (mode==0 && add_ext[W]==0);          // add without overflow
  cover property (mode==0 && add_ext[W]==1);          // add with overflow
  cover property (mode==1 && sub_ext[W]==0);          // sub without borrow (A>=B)
  cover property (mode==1 && sub_ext[W]==1);          // sub with borrow (A<B)
  cover property (mode==0 && A==0 && B==0);           // 0+0
  cover property (mode==0 && A=='1 && B=='1);         // max+max
  cover property (mode==1 && A=='0 && B=='1);         // 0 - max
  cover property (mode==1 && A=='1 && B=='0);         // max - 0

endmodule

// Example bind (adjust clk/rst_n names to your TB):
// bind adder_subtractor adder_subtractor_sva #(.W(4)) sva_i (.*, .clk(tb_clk), .rst_n(tb_rst_n));