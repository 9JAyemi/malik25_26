// SVA checker for IBUF_IBUFDISABLE
// Bind this to the DUT instance(s).

module IBUF_IBUFDISABLE_sva
  #(parameter string IBUF_LOW_PWR   = "TRUE",
              string IOSTANDARD    = "DEFAULT",
              string SIM_DEVICE    = "7SERIES",
              string USE_IBUFDISABLE = "TRUE")
  (input logic O, I, IBUFDISABLE);

  // Static parameter legality checks (one-time)
  initial begin
    assert (IBUF_LOW_PWR == "TRUE" || IBUF_LOW_PWR == "FALSE")
      else $error("IBUF_LOW_PWR must be TRUE or FALSE");
    assert (USE_IBUFDISABLE == "TRUE" || USE_IBUFDISABLE == "FALSE")
      else $error("USE_IBUFDISABLE must be TRUE or FALSE");
    assert (SIM_DEVICE == "7SERIES"      ||
            SIM_DEVICE == "ULTRASCALE"   ||
            SIM_DEVICE == "VERSAL_AI_CORE" || SIM_DEVICE == "VERSAL_AI_CORE_ES1" || SIM_DEVICE == "VERSAL_AI_CORE_ES2" ||
            SIM_DEVICE == "VERSAL_AI_EDGE" || SIM_DEVICE == "VERSAL_AI_EDGE_ES1" || SIM_DEVICE == "VERSAL_AI_EDGE_ES2" ||
            SIM_DEVICE == "VERSAL_AI_RF"   || SIM_DEVICE == "VERSAL_AI_RF_ES1"   || SIM_DEVICE == "VERSAL_AI_RF_ES2"   ||
            SIM_DEVICE == "VERSAL_HBM"     || SIM_DEVICE == "VERSAL_HBM_ES1"     || SIM_DEVICE == "VERSAL_HBM_ES2"     ||
            SIM_DEVICE == "VERSAL_PREMIUM" || SIM_DEVICE == "VERSAL_PREMIUM_ES1" || SIM_DEVICE == "VERSAL_PREMIUM_ES2" ||
            SIM_DEVICE == "VERSAL_PRIME"   || SIM_DEVICE == "VERSAL_PRIME_ES1"   || SIM_DEVICE == "VERSAL_PRIME_ES2")
      else $error("Illegal SIM_DEVICE value: %s", SIM_DEVICE);
  end

  // Constants derived from parameters
  localparam bit USE_EN   = (USE_IBUFDISABLE == "TRUE");
  localparam bit OUTVAL   = (SIM_DEVICE == "7SERIES") ? 1'b1 : 1'b0;

  // Functional correctness
  // USE_IBUFDISABLE == TRUE, pass-through when IBUFDISABLE==0
  assert property (@(I or IBUFDISABLE)
                   USE_EN && (IBUFDISABLE === 1'b0) |=> (O === I))
    else $error("O must follow I when IBUFDISABLE==0");

  // USE_IBUFDISABLE == TRUE, force OUTVAL when IBUFDISABLE==1
  assert property (@(I or IBUFDISABLE)
                   USE_EN && (IBUFDISABLE === 1'b1) |=> (O === OUTVAL))
    else $error("O must be OUTVAL when IBUFDISABLE==1");

  // USE_IBUFDISABLE == TRUE, unknown disable drives X
  assert property (@(I or IBUFDISABLE)
                   USE_EN && (IBUFDISABLE !== 1'b0) && (IBUFDISABLE !== 1'b1) |=> $isunknown(O))
    else $error("O must be X when IBUFDISABLE is X/Z");

  // USE_IBUFDISABLE == FALSE, always pass-through
  assert property (@(I or IBUFDISABLE)
                   !USE_EN |=> (O === I))
    else $error("O must always follow I when USE_IBUFDISABLE==FALSE");

  // Stability w.r.t. I when disabled
  assert property (@(I) USE_EN && (IBUFDISABLE === 1'b1) |=> (O === OUTVAL))
    else $error("O must ignore I when IBUFDISABLE==1");

  // Coverage
  cover property (@(IBUFDISABLE) USE_EN && (IBUFDISABLE === 1'b0));
  cover property (@(IBUFDISABLE) USE_EN && (IBUFDISABLE === 1'b1));
  cover property (@(IBUFDISABLE) USE_EN && $rose(IBUFDISABLE));
  cover property (@(IBUFDISABLE) USE_EN && $fell(IBUFDISABLE));
  cover property (@(I) USE_EN && (IBUFDISABLE === 1'b0) && $changed(I));
  cover property (@(I) USE_EN && (IBUFDISABLE === 1'b1) && $changed(I));
  cover property (@(IBUFDISABLE) USE_EN && $isunknown(IBUFDISABLE));

endmodule

// Bind to all instances (override parameters from DUT)
bind IBUF_IBUFDISABLE IBUF_IBUFDISABLE_sva
  #(.IBUF_LOW_PWR(IBUF_LOW_PWR),
    .IOSTANDARD(IOSTANDARD),
    .SIM_DEVICE(SIM_DEVICE),
    .USE_IBUFDISABLE(USE_IBUFDISABLE))
  IBUF_IBUFDISABLE_sva_b(.O(O), .I(I), .IBUFDISABLE(IBUFDISABLE));