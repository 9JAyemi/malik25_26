// SVA for digital_circuit
// Binds into the DUT, checks function/structure under good power, adds coverage.

module digital_circuit_sva (
  input  logic A1,
  input  logic A2,
  input  logic B1_N,
  input  logic VPWR,
  input  logic VGND,
  input  logic VPB,
  input  logic VNB,
  input  logic b,
  input  logic and0_out,
  input  logic nor0_out_Y,
  input  logic pwrgood_pp0_out_Y,
  input  logic Y
);

  function automatic bit power_good();
    return (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);
  endfunction

  // Structural and functional checks (combinational, power-good only)
  always_comb begin
    if (power_good()) begin
      assert (b === ~B1_N) else $error("%m b != ~B1_N");
      assert (and0_out === (A1 & A2)) else $error("%m and0_out != A1 & A2");
      assert (nor0_out_Y === ~(b | and0_out)) else $error("%m nor0_out_Y mismatch");
      assert (pwrgood_pp0_out_Y === nor0_out_Y) else $error("%m pwrgood buf mismatch");
      assert (Y === ~( (~B1_N) | (A1 & A2) )) else $error("%m Y functional mismatch");

      if (!$isunknown({A1,A2,B1_N}))
        assert (!$isunknown(Y)) else $error("%m Y is X with known inputs");

      // Deterministic cases (4-state robust)
      if (B1_N===1'b0) assert (Y===1'b0) else $error("%m Y must be 0 when B1_N=0");
      if ((B1_N===1'b1) && (A1===1'b1) && (A2===1'b1))
        assert (Y===1'b0) else $error("%m Y must be 0 when B1_N=1 & A1=1 & A2=1");
      if ((B1_N===1'b1) && ((A1===1'b0)||(A2===1'b0)))
        assert (Y===1'b1) else $error("%m Y must be 1 when B1_N=1 and any A=0");
    end
  end

  // Y changes only if inputs change (under good power)
  property y_changes_only_if_inputs_change;
    @(Y or A1 or A2 or B1_N) disable iff (!power_good())
      $changed(Y) |-> $changed({A1,A2,B1_N});
  endproperty
  assert property (y_changes_only_if_inputs_change);

  // Cover all 8 input combinations and expected Y under power_good
  generate
    genvar i;
    for (i=0;i<8;i++) begin: cov_inputs
      localparam bit a1  = ((i>>2)&1);
      localparam bit a2  = ((i>>1)&1);
      localparam bit b1n = ((i>>0)&1);
      cover property (@(A1 or A2 or B1_N)
        power_good() &&
        (A1===a1) && (A2===a2) && (B1_N===b1n) &&
        (Y === (b1n & (~a1 | ~a2)))
      );
    end
  endgenerate

  // Cover Y edges and power-good observed
  cover property (@(posedge Y) power_good());
  cover property (@(negedge Y) power_good());
  cover property (@(VPWR or VGND or VPB or VNB) power_good());

endmodule

bind digital_circuit digital_circuit_sva sva_i (
  .A1(A1), .A2(A2), .B1_N(B1_N),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
  .b(b), .and0_out(and0_out), .nor0_out_Y(nor0_out_Y), .pwrgood_pp0_out_Y(pwrgood_pp0_out_Y),
  .Y(Y)
);