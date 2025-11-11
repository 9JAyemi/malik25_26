// SVA for mux: functional checks, X-propagation, and compact coverage.
// Uses $global_clock to sample combinational behavior; ##0 avoids race with RHS updates.

module mux_sva (
  input logic [7:0] in0,
  input logic [7:0] in1,
  input logic [7:0] in2,
  input logic [7:0] in3,
  input logic [1:0] sel,
  input logic       en,
  input logic [7:0] out
);
  default clocking cb @(posedge $global_clock); endclocking

  // Basic functional correctness
  a_dis_zero:  assert property ((!$isunknown(en) && !en)            |-> ##0 (out == '0));
  a_sel_00:    assert property ((!$isunknown({en,sel}) && en && sel==2'b00 && !$isunknown(in0)) |-> ##0 (out == in0));
  a_sel_01:    assert property ((!$isunknown({en,sel}) && en && sel==2'b01 && !$isunknown(in1)) |-> ##0 (out == in1));
  a_sel_10:    assert property ((!$isunknown({en,sel}) && en && sel==2'b10 && !$isunknown(in2)) |-> ##0 (out == in2));
  a_sel_11:    assert property ((!$isunknown({en,sel}) && en && sel==2'b11 && !$isunknown(in3)) |-> ##0 (out == in3));

  // X-propagation when selected input is unknown (and control is known)
  a_x_00:      assert property ((!$isunknown({en,sel}) && en && sel==2'b00 &&  $isunknown(in0)) |-> ##0 $isunknown(out));
  a_x_01:      assert property ((!$isunknown({en,sel}) && en && sel==2'b01 &&  $isunknown(in1)) |-> ##0 $isunknown(out));
  a_x_10:      assert property ((!$isunknown({en,sel}) && en && sel==2'b10 &&  $isunknown(in2)) |-> ##0 $isunknown(out));
  a_x_11:      assert property ((!$isunknown({en,sel}) && en && sel==2'b11 &&  $isunknown(in3)) |-> ##0 $isunknown(out));

  // Optional: flag X/Z on control at any time
  a_ctrl_known: assert property (1'b1 |-> ##0 !$isunknown({en,sel}));

  // Compact functional coverage
  c_dis_zero:   cover property (!en ##0 (out == '0));
  c_sel_00:     cover property (en && sel==2'b00 ##0 (out == in0));
  c_sel_01:     cover property (en && sel==2'b01 ##0 (out == in1));
  c_sel_10:     cover property (en && sel==2'b10 ##0 (out == in2));
  c_sel_11:     cover property (en && sel==2'b11 ##0 (out == in3));
endmodule

// Bind into DUT
bind mux mux_sva mux_sva_i (.*);