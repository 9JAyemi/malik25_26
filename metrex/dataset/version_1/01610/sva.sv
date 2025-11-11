// SVA for mux4_ctrl
// Bind-in checker; event-based sampling for combinational DUT

module mux4_ctrl_sva(
  input logic [7:0] A, B, C, D,
  input logic       ctrl,
  input logic [7:0] out
);
  // Sample on any relevant change
  default clocking cb @(A or B or C or D or ctrl or out); endclocking

  // Functional mapping
  a_sel0:      assert property (ctrl === 1'b0 |-> (out === A));
  a_sel1:      assert property (ctrl === 1'b1 |-> (out === D));
  a_default:   assert property ($isunknown(ctrl) |-> (out === 8'h00));

  // Zero-delay data following
  a_follows_A: assert property ((ctrl === 1'b0 && $changed(A)) |-> ##0 (out === A));
  a_follows_D: assert property ((ctrl === 1'b1 && $changed(D)) |-> ##0 (out === D));

  // Zero-delay control switching
  a_ctrl_rise: assert property ($rose(ctrl) |-> ##0 (out === D));
  a_ctrl_fall: assert property ($fell(ctrl) |-> ##0 (out === A));

  // Output changes only due to selected input (when ctrl stable)
  a_out_cause_A: assert property ((ctrl === 1'b0 && $stable(ctrl) && $changed(out)) |-> $changed(A));
  a_out_cause_D: assert property ((ctrl === 1'b1 && $stable(ctrl) && $changed(out)) |-> $changed(D));

  // Non-interference of unused inputs B and C
  a_B_noeff: assert property (($changed(B) && $stable(A) && $stable(D) && $stable(ctrl)) |-> ##0 $stable(out));
  a_C_noeff: assert property (($changed(C) && $stable(A) && $stable(D) && $stable(ctrl)) |-> ##0 $stable(out));

  // Coverage
  c_sel0:        cover property (ctrl === 1'b0 && out === A);
  c_sel1:        cover property (ctrl === 1'b1 && out === D);
  c_default:     cover property ($isunknown(ctrl) && out === 8'h00);
  c_A_pass:      cover property (ctrl === 1'b0 && $changed(A) && out === A);
  c_D_pass:      cover property (ctrl === 1'b1 && $changed(D) && out === D);
  c_ctrl_01:     cover property ($rose(ctrl) && out === D);
  c_ctrl_10:     cover property ($fell(ctrl) && out === A);
  c_BC_noeff:    cover property ((($changed(B) || $changed(C)) && $stable(A) && $stable(D) && $stable(ctrl) && $stable(out)));
endmodule

bind mux4_ctrl mux4_ctrl_sva sva_i(.A(A), .B(B), .C(C), .D(D), .ctrl(ctrl), .out(out));