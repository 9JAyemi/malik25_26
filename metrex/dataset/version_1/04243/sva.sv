// SVA for nand4: spec- and structure-level checks with concise coverage.
// Bind this module to the DUT: bind nand4 nand4_sva u_nand4_sva (.*);

module nand4_sva (
  input logic A, B, C, D,
  input logic VPWR, VGND,
  input logic Y,
  // bind to internals for structural checks
  input logic nand1_out, nand2_out, nand3_out
);

  // Trigger on any relevant change
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge D or negedge D or
    posedge VPWR or negedge VPWR or
    posedge VGND or negedge VGND
  ); endclocking

  // Power-good qualifier (only check when rails are exactly valid)
  logic pgood;
  assign pgood = (VPWR === 1'b1) && (VGND === 1'b0);

  // Spec-level functional check: 4-input NAND truth function
  property p_func;
    disable iff (!pgood)
      !$isunknown({A,B,C,D}) |-> (Y === ~(A & B & C & D));
  endproperty
  assert property (p_func);

  // Dominant-zero and all-ones corner checks (helpful for debug)
  assert property (disable iff (!pgood)
    ((A===1'b0)||(B===1'b0)||(C===1'b0)||(D===1'b0)) |-> (Y===1'b1));
  assert property (disable iff (!pgood)
    (A===1'b1 && B===1'b1 && C===1'b1 && D===1'b1) |-> (Y===1'b0));

  // X-propagation sanity: if no input is 0 and at least one is X/Z, Y must be X
  assert property (disable iff (!pgood)
    ($isunknown({A,B,C,D}) &&
     (A!==1'b0)&&(B!==1'b0)&&(C!==1'b0)&&(D!==1'b0)) |-> $isunknown(Y));

  // Structural consistency with internal gates (localize issues fast)
  assert property (disable iff (!pgood) (nand1_out === ~(A & B)));
  assert property (disable iff (!pgood) (nand2_out === ~(C & D)));
  assert property (disable iff (!pgood) (nand3_out === ~(nand1_out & nand2_out)));
  assert property (disable iff (!pgood) (Y === ~nand3_out));

  // Minimal, meaningful coverage
  cover property (pgood && (Y===1'b1));
  cover property (pgood && (Y===1'b0));
  cover property (pgood && (A===0 && B===1 && C===1 && D===1 && Y===1));
  cover property (pgood && (B===0 && A===1 && C===1 && D===1 && Y===1));
  cover property (pgood && (C===0 && A===1 && B===1 && D===1 && Y===1));
  cover property (pgood && (D===0 && A===1 && B===1 && C===1 && Y===1));
  cover property (pgood && (A===1 && B===1 && C===1 && D===1 && Y===0));
  // Sensitization to unknowns (no 0s present)
  cover property (pgood &&
                  $isunknown({A,B,C,D}) &&
                  (A!==0)&&(B!==0)&&(C!==0)&&(D!==0) && $isunknown(Y));

  // Simple toggle coverage on Y under power-good
  cover property (pgood && Y===1 ##1 pgood && Y===0);
  cover property (pgood && Y===0 ##1 pgood && Y===1);

endmodule

// Example bind (connects to internals by name for structural checks)
bind nand4 nand4_sva u_nand4_sva (
  .A(A), .B(B), .C(C), .D(D), .VPWR(VPWR), .VGND(VGND), .Y(Y),
  .nand1_out(nand1_out), .nand2_out(nand2_out), .nand3_out(nand3_out)
);