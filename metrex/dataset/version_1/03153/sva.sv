// SVA for sky130_fd_sc_ls__clkdlyinv5sd1 (Y = ~A), with power checks, X-prop, and coverage

module sky130_fd_sc_ls__clkdlyinv5sd1_sva (
  input logic A, Y,
  input logic VPWR, VGND, VPB, VNB
);
  logic pwr_ok;
  assign pwr_ok = (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);

  default clocking cb @(A or Y or VPWR or VGND or VPB or VNB); endclocking

  // Power integrity must hold whenever we sample
  a_pwr_ok:        assert property (pwr_ok);

  // Functional correctness and X-propagation
  a_func_known:    assert property (disable iff (!pwr_ok) (!$isunknown(A)) |-> (Y === ~A));
  a_xprop:         assert property (disable iff (!pwr_ok)  $isunknown(A)   |->  $isunknown(Y));

  // No spurious Y activity without A activity
  a_no_spur_y:     assert property (disable iff (!pwr_ok) !$changed(A) |-> !$changed(Y));

  // Edge-direction consistency
  a_posedge:       assert property (disable iff (!pwr_ok) @(posedge A) Y === 1'b0);
  a_negedge:       assert property (disable iff (!pwr_ok) @(negedge A) Y === 1'b1);

  // Coverage
  c_a_rise_y_fall: cover  property (disable iff (!pwr_ok) @(posedge A) $fell(Y));
  c_a_fall_y_rise: cover  property (disable iff (!pwr_ok) @(negedge A) $rose(Y));
  c_known_0_1:     cover  property (disable iff (!pwr_ok) (A===1'b0 && Y===1'b1));
  c_known_1_0:     cover  property (disable iff (!pwr_ok) (A===1'b1 && Y===1'b0));
  c_x_path:        cover  property (disable iff (!pwr_ok) $isunknown(A) ##1 $isunknown(Y));
endmodule

bind sky130_fd_sc_ls__clkdlyinv5sd1
  sky130_fd_sc_ls__clkdlyinv5sd1_sva
    u_sva (.A(A), .Y(Y), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB));