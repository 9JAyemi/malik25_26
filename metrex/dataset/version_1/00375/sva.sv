// SVA bind module for QPSK_Demodulator_Baseband (combinational checks, concise but complete)
module QPSK_Demodulator_Baseband_sva (
  input  logic               signed [15:0] in0_re,
  input  logic               signed [15:0] in0_im,
  input  logic                      [1:0] out0,
  input  logic                             inphase_lt_zero,
  input  logic                             inphase_eq_zero,
  input  logic                             quadrature_lt_zero,
  input  logic                             quadrature_eq_zero,
  input  logic                      [3:0] decisionLUTaddr,
  input  logic                      [1:0] hardDecision,
  input  logic                      [1:0] DirectLookupTable_1 [0:15]
);

  // Immediate assertions: pure combinational correctness
  always_comb begin
    // No X/Z on primary I/Os and key internal nets
    assert (!$isunknown(in0_re) && !$isunknown(in0_im)) else $error("Inputs unknown");
    assert (!$isunknown(out0)) else $error("Output unknown");
    assert (!$isunknown({inphase_lt_zero,inphase_eq_zero,quadrature_lt_zero,quadrature_eq_zero})) else $error("Sign flags unknown");
    assert (!$isunknown(decisionLUTaddr) && !$isunknown(hardDecision)) else $error("LUT addr/decision unknown");

    // Sign flag correctness and mutual exclusion
    assert (inphase_lt_zero == (in0_re < 0)) else $error("inphase_lt_zero mismatch");
    assert (inphase_eq_zero == (in0_re == 0)) else $error("inphase_eq_zero mismatch");
    assert (!(inphase_lt_zero && inphase_eq_zero)) else $error("inphase lt&eq both 1");

    assert (quadrature_lt_zero == (in0_im < 0)) else $error("quadrature_lt_zero mismatch");
    assert (quadrature_eq_zero == (in0_im == 0)) else $error("quadrature_eq_zero mismatch");
    assert (!(quadrature_lt_zero && quadrature_eq_zero)) else $error("quadrature lt&eq both 1");

    // Address formation and LUT/outputs consistency
    assert (decisionLUTaddr == {inphase_lt_zero, inphase_eq_zero, quadrature_lt_zero, quadrature_eq_zero})
      else $error("decisionLUTaddr mismatch");
    assert (hardDecision == DirectLookupTable_1[decisionLUTaddr]) else $error("hardDecision != LUT");
    assert (out0 == hardDecision) else $error("out0 != hardDecision");

    // Functional mapping checks for all reachable sign/zero combinations (9 cases)
    // Re>0, Im>0 -> 00
    assert ((!inphase_lt_zero && !inphase_eq_zero && !quadrature_lt_zero && !quadrature_eq_zero) -> (out0 == 2'b00))
      else $error("Re>0,Im>0 mapping wrong");
    // Re>0, Im=0 -> 00
    assert ((!inphase_lt_zero && !inphase_eq_zero && !quadrature_lt_zero &&  quadrature_eq_zero) -> (out0 == 2'b00))
      else $error("Re>0,Im=0 mapping wrong");
    // Re>0, Im<0 -> 10
    assert ((!inphase_lt_zero && !inphase_eq_zero &&  quadrature_lt_zero && !quadrature_eq_zero) -> (out0 == 2'b10))
      else $error("Re>0,Im<0 mapping wrong");

    // Re=0, Im>0 -> 01
    assert ((!inphase_lt_zero &&  inphase_eq_zero && !quadrature_lt_zero && !quadrature_eq_zero) -> (out0 == 2'b01))
      else $error("Re=0,Im>0 mapping wrong");
    // Re=0, Im=0 -> 00
    assert ((!inphase_lt_zero &&  inphase_eq_zero && !quadrature_lt_zero &&  quadrature_eq_zero) -> (out0 == 2'b00))
      else $error("Re=0,Im=0 mapping wrong");
    // Re=0, Im<0 -> 10
    assert ((!inphase_lt_zero &&  inphase_eq_zero &&  quadrature_lt_zero && !quadrature_eq_zero) -> (out0 == 2'b10))
      else $error("Re=0,Im<0 mapping wrong");

    // Re<0, Im>0 -> 01
    assert (( inphase_lt_zero && !inphase_eq_zero && !quadrature_lt_zero && !quadrature_eq_zero) -> (out0 == 2'b01))
      else $error("Re<0,Im>0 mapping wrong");
    // Re<0, Im=0 -> 11
    assert (( inphase_lt_zero && !inphase_eq_zero && !quadrature_lt_zero &&  quadrature_eq_zero) -> (out0 == 2'b11))
      else $error("Re<0,Im=0 mapping wrong");
    // Re<0, Im<0 -> 11
    assert (( inphase_lt_zero && !inphase_eq_zero &&  quadrature_lt_zero && !quadrature_eq_zero) -> (out0 == 2'b11))
      else $error("Re<0,Im<0 mapping wrong");

    // Functional coverage (reachable cases and all output symbols)
    cover (!inphase_lt_zero && !inphase_eq_zero && !quadrature_lt_zero && !quadrature_eq_zero); // +/+
    cover (!inphase_lt_zero && !inphase_eq_zero &&  quadrature_lt_zero && !quadrature_eq_zero); // +/-
    cover (!inphase_lt_zero &&  inphase_eq_zero && !quadrature_lt_zero && !quadrature_eq_zero); // 0/+
    cover (!inphase_lt_zero &&  inphase_eq_zero &&  quadrature_lt_zero && !quadrature_eq_zero); // 0/-
    cover ( inphase_lt_zero && !inphase_eq_zero && !quadrature_lt_zero && !quadrature_eq_zero); // -/+
    cover ( inphase_lt_zero && !inphase_eq_zero &&  quadrature_lt_zero && !quadrature_eq_zero); // -/-
    cover (!inphase_lt_zero && !inphase_eq_zero && !quadrature_lt_zero &&  quadrature_eq_zero); // +/0
    cover ( inphase_lt_zero && !inphase_eq_zero && !quadrature_lt_zero &&  quadrature_eq_zero); // -/0
    cover (!inphase_lt_zero &&  inphase_eq_zero && !quadrature_lt_zero &&  quadrature_eq_zero); // 0/0

    cover (out0 == 2'b00);
    cover (out0 == 2'b01);
    cover (out0 == 2'b10);
    cover (out0 == 2'b11);
  end

endmodule

// Bind into the DUT (no clock required; purely combinational)
bind QPSK_Demodulator_Baseband QPSK_Demodulator_Baseband_sva sva_i (
  .in0_re(in0_re),
  .in0_im(in0_im),
  .out0(out0),
  .inphase_lt_zero(inphase_lt_zero),
  .inphase_eq_zero(inphase_eq_zero),
  .quadrature_lt_zero(quadrature_lt_zero),
  .quadrature_eq_zero(quadrature_eq_zero),
  .decisionLUTaddr(decisionLUTaddr),
  .hardDecision(hardDecision),
  .DirectLookupTable_1(DirectLookupTable_1)
);