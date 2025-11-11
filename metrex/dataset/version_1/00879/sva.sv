// SVA for sky130_fd_sc_hd__clkinvlp (Y = ~A), with power-rail checks and concise coverage

module sky130_fd_sc_hd__clkinvlp_sva (
  input logic A,
  input logic Y,
  input logic VPWR, VGND, VPB, VNB
);
  // Sample on any edge of A or Y
  default clocking cb @(posedge A or negedge A or posedge Y or negedge Y); endclocking

  // Power rails must be valid constants
  ap_rails_const: assert property (1'b1 |-> (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0));

  // Functional inversion whenever A is known (settled same timestep)
  ap_func: assert property (!$isunknown(A) |-> ##0 (! $isunknown(Y) && Y === ~A));

  // Any A change drives a corresponding Y change (no missing toggle, correct value)
  ap_a_change_drives_y: assert property ($changed(A) |-> ##0 ($changed(Y) && Y === ~A));

  // Y only changes if A changed (no spurious glitches)
  ap_y_change_due_to_a: assert property ($changed(Y) |-> ##0 $changed(A));

  // No X/Z on Y when rails are good and A is 0/1
  ap_no_x_on_y: assert property ((VPWR===1 && VGND===0 && VPB===1 && VNB===0 && !$isunknown(A)) |-> ##0 (!$isunknown(Y)));

  // Coverage: both polarities and both states observed
  cp_rise_fall: cover property ($rose(A) ##0 $fell(Y));
  cp_fall_rise: cover property ($fell(A) ##0 $rose(Y));
  cp_state0:    cover property (!$isunknown(A) && A==1'b0 && Y==1'b1);
  cp_state1:    cover property (!$isunknown(A) && A==1'b1 && Y==1'b0);
endmodule

// Bind into the DUT
bind sky130_fd_sc_hd__clkinvlp sky130_fd_sc_hd__clkinvlp_sva i_sva (
  .A(A), .Y(Y), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);