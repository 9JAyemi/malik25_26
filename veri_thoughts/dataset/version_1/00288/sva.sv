// SVA for sky130_fd_sc_lp__o32ai (Y = ~((A1|A2|A3) & (B1|B2)))
// Bindable checker with concise functional, structural, X, and coverage checks.

module sky130_fd_sc_lp__o32ai_sva #(
  parameter bit CHECK_INTERNALS = 1
)(
  input logic Y,
  input logic A1, A2, A3,
  input logic B1, B2,
  input logic VPWR, VGND, VPB, VNB,
  // internal observability (bound by name)
  input logic nor0_out,
  input logic nor1_out,
  input logic or0_out_Y
);

  // Sample on any input change (both edges) to avoid race; use ##0 in properties.
  default clocking cb @(
      posedge A1 or negedge A1 or
      posedge A2 or negedge A2 or
      posedge A3 or negedge A3 or
      posedge B1 or negedge B1 or
      posedge B2 or negedge B2
  ); endclocking

  // Power-good
  logic pgood;
  always_comb pgood = (VPWR===1'b1) && (VPB===1'b1) && (VGND===1'b0) && (VNB===1'b0);

  // Helper reductions
  logic a_or, b_or, f;
  always_comb begin
    a_or = (A1 | A2 | A3);
    b_or = (B1 | B2);
    f    = ~(a_or & b_or);
  end

  // Functional equivalence (4-state, sampled after delta to avoid races)
  property p_func;
    pgood |-> ##0 (Y === f);
  endproperty
  assert property (p_func);

  // Knownness: if inputs are known, output must be known
  property p_known;
    pgood && !$isunknown({A1,A2,A3,B1,B2}) |-> ##0 !$isunknown(Y);
  endproperty
  assert property (p_known);

  // Fast combinational immediate checks (redundant with p_func but tightens delta behavior)
  always_comb if (pgood) begin
    assert (#0 (Y === f)) else $error("o32ai functional mismatch");
  end

  // Structural internal checks (only if bound with internals visible)
  generate if (CHECK_INTERNALS) begin
    always_comb if (pgood) begin
      assert (#0 (nor0_out   === ~a_or))        else $error("nor0_out mismatch");
      assert (#0 (nor1_out   === ~b_or))        else $error("nor1_out mismatch");
      assert (#0 (or0_out_Y  === (nor0_out|nor1_out))) else $error("or0_out_Y mismatch");
      assert (#0 (Y          === or0_out_Y))    else $error("buf/Y mismatch");
    end
  end endgenerate

  // Essential functional corner covers
  cover property (pgood &&  a_or &&  b_or ##0 (Y===1'b0)); // only case Y=0
  cover property (pgood && !a_or &&  b_or ##0 (Y===1'b1));
  cover property (pgood &&  a_or && !b_or ##0 (Y===1'b1));
  cover property (pgood && !a_or && !b_or ##0 (Y===1'b1));

  // Output toggle coverage
  cover property (pgood && $rose(Y));
  cover property (pgood && $fell(Y));

  // Correlate Y change with driving group truth changes
  cover property (pgood && $changed(a_or) && ##0 $changed(Y));
  cover property (pgood && $changed(b_or) && ##0 $changed(Y));

endmodule

// Bind into the DUT; internal nets are connected for structural checks.
bind sky130_fd_sc_lp__o32ai sky130_fd_sc_lp__o32ai_sva
  #(.CHECK_INTERNALS(1))
  o32ai_sva_i (
    .Y(Y),
    .A1(A1), .A2(A2), .A3(A3),
    .B1(B1), .B2(B2),
    .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
    .nor0_out(nor0_out), .nor1_out(nor1_out), .or0_out_Y(or0_out_Y)
  );