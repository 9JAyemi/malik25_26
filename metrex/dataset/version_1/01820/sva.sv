// SVA checker for sky130_fd_sc_ms__a21o
module sky130_fd_sc_ms__a21o_sva (
  input logic A1, A2, B1, X,
  input logic VPB, VPWR, VGND, VNB
);
  // Sample on any relevant signal edge (combinational cell)
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge B1 or negedge B1 or
    posedge VPWR or negedge VPWR or
    posedge VGND or negedge VGND or
    posedge VPB  or negedge VPB  or
    posedge VNB  or negedge VNB
  ); endclocking

  // Simple power-good gate
  wire pwr_good = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);

  // Functional equivalence (logic simplifies to X == A1 ^ B1)
  property p_func;
    disable iff (!pwr_good)
      !$isunknown({A1,B1}) |-> (X === (A1 ^ B1));
  endproperty
  assert property (p_func);

  // Output must be known when inputs are known and power is good
  property p_known_out;
    disable iff (!pwr_good)
      !$isunknown({A1,B1}) |-> !$isunknown(X);
  endproperty
  assert property (p_known_out);

  // Independence from A2 (and unrelated rails) under stable A1/B1
  property p_no_dep_A2;
    disable iff (!pwr_good)
      $changed(A2) && $stable({A1,B1}) |-> $stable(X);
  endproperty
  assert property (p_no_dep_A2);

  // Output changes only when A1 or B1 changes (not due to A2)
  property p_out_changes_on_dataonly;
    disable iff (!pwr_good)
      $changed(X) |-> ($changed(A1) || $changed(B1));
  endproperty
  assert property (p_out_changes_on_dataonly);

  // Toggle responsiveness: flipping one data input with the other stable flips X
  property p_resp_A1;
    disable iff (!pwr_good)
      $changed(A1) && $stable(B1) && !$isunknown({A1,B1}) |-> $changed(X);
  endproperty
  assert property (p_resp_A1);

  property p_resp_B1;
    disable iff (!pwr_good)
      $changed(B1) && $stable(A1) && !$isunknown({A1,B1}) |-> $changed(X);
  endproperty
  assert property (p_resp_B1);

  // Functional coverage
  cover property (pwr_good && (A1==1'b0) && (B1==1'b0) && (X==1'b0));
  cover property (pwr_good && (A1==1'b0) && (B1==1'b1) && (X==1'b1));
  cover property (pwr_good && (A1==1'b1) && (B1==1'b0) && (X==1'b1));
  cover property (pwr_good && (A1==1'b1) && (B1==1'b1) && (X==1'b0));

  // Cover independence of A2: toggle A2 with X stable while A1/B1 stable
  cover property (pwr_good && $stable({A1,B1}) ##1 $changed(A2) ##0 $stable(X));
endmodule

// Bind into DUT
bind sky130_fd_sc_ms__a21o sky130_fd_sc_ms__a21o_sva i_sva (.*);