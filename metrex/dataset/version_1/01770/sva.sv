// SVA checker for data_power_module
// Binds into the DUT; focuses on functional equivalence, power gating, stability, X-prop, and key coverage.
bind data_power_module data_power_module_sva u_data_power_module_sva();

module data_power_module_sva;

  // Mirror of the captured data bit (what data_reg[0] effectively holds)
  logic exp_bit;
  always @(posedge VPB) exp_bit <= A;

  // 1) Functional equivalence: X must equal captured A bit AND VPWR at all relevant events
  // Evaluate on any driver change to catch mid-cycle issues
  property p_func_equiv;
    @(A or VPWR or posedge VPB or negedge VPB)
      X == (exp_bit & VPWR);
  endproperty
  assert property (p_func_equiv);

  // 2) Power gating safety: when VPWR is 0, X must be 0
  property p_power_off_forces_zero;
    @(A or VPWR or posedge VPB or negedge VPB)
      (VPWR == 1'b0) |-> (X == 1'b0);
  endproperty
  assert property (p_power_off_forces_zero);

  // 3) Change-causality: X may only change if exp_bit or VPWR changes
  property p_x_changes_only_from_sources;
    @(X) $changed(exp_bit) or $changed(VPWR);
  endproperty
  assert property (p_x_changes_only_from_sources);

  // 4) No X/Z on output when inputs are known
  property p_no_x_when_inputs_known;
    @(A or VPWR or posedge VPB or negedge VPB)
      (!$isunknown({exp_bit, VPWR})) |-> !$isunknown(X);
  endproperty
  assert property (p_no_x_when_inputs_known);

  // 5) Width/truncation intent: upper bits of data_reg must stay 0 (given 1-bit A assignment)
  // Immediate assertion keeps it delta-safe around clock edges
  always @* begin
    assert (data_reg[7:1] == '0)
      else $error("data_reg[7:1] not zero as intended by 1-bit load");
  end

  // 6) Basic rail sanity assumptions (optional; comment out if not desired)
  // These constrain typical legal states for formal and prevent spurious X-prop
  assume property (@(posedge VPB) (VGND == 1'b0) && (VNB == 1'b0));
  assume property (@(posedge VPB) (VPWR inside {1'b0,1'b1}));

  // Coverage

  // Capture both A values over successive clocks
  cover property (@(posedge VPB) (A==0) ##1 (A==1));
  cover property (@(posedge VPB) (A==1) ##1 (A==0));

  // Observe power gating behavior in both states
  cover property (@(posedge VPB) (VPWR==0 && X==0));
  cover property (@(posedge VPB) (VPWR==1 && X==exp_bit));

  // Power toggle seen
  cover property (@(posedge VPB) (VPWR==0) ##1 (VPWR==1));
  cover property (@(posedge VPB) (VPWR==1) ##1 (VPWR==0));

  // X activity
  cover property (@(X) $rose(X));
  cover property (@(X) $fell(X));

endmodule