// SVA for sky130_fd_sc_ms__nand4
// Bind these assertions to the DUT; no clock required (combinational checks).

module sky130_fd_sc_ms__nand4_sva (input logic Y, A, B, C, D);

  // Functional equivalence (4‑state, delta-cycle settle)
  always @* begin
    assert (#0 (Y === ~&{A,B,C,D}))
      else $error("NAND4 func mismatch: Y=%b A=%b B=%b C=%b D=%b", Y, A, B, C, D);
  end

  // Event for concurrent checks/coverage on any input edge
  localparam bit UNUSED = 1'b0;
  // expand to all input edges
  `define ANY_IN_EDGE posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D

  // Any 0 dominates -> Y must be 1
  property p_any0_forces1;
    @(`ANY_IN_EDGE)
      ((A===1'b0)||(B===1'b0)||(C===1'b0)||(D===1'b0)) |-> ##0 (Y===1'b1);
  endproperty
  assert property (p_any0_forces1)
    else $error("NAND4: known 0 did not force Y=1");

  // All ones -> Y must be 0
  property p_all1_forces0;
    @(`ANY_IN_EDGE)
      ((A===1'b1)&&(B===1'b1)&&(C===1'b1)&&(D===1'b1)) |-> ##0 (Y===1'b0);
  endproperty
  assert property (p_all1_forces0)
    else $error("NAND4: all 1s did not force Y=0");

  // X/Z propagation when no known 0 present
  property p_xprop_no_zero;
    @(`ANY_IN_EDGE)
      ($isunknown({A,B,C,D}) && !((A===1'b0)||(B===1'b0)||(C===1'b0)||(D===1'b0))) |-> ##0 (Y===1'bx);
  endproperty
  assert property (p_xprop_no_zero)
    else $error("NAND4: X/Z input without any 0 did not yield Y=X");

  // Edge reflections when other inputs are 1: Y = ~toggling input
  property p_edgeA_reflects;
    @(posedge A or negedge A) (B===1 && C===1 && D===1) |-> ##0 (Y === ~A);
  endproperty
  property p_edgeB_reflects;
    @(posedge B or negedge B) (A===1 && C===1 && D===1) |-> ##0 (Y === ~B);
  endproperty
  property p_edgeC_reflects;
    @(posedge C or negedge C) (A===1 && B===1 && D===1) |-> ##0 (Y === ~C);
  endproperty
  property p_edgeD_reflects;
    @(posedge D or negedge D) (A===1 && B===1 && C===1) |-> ##0 (Y === ~D);
  endproperty

  assert property (p_edgeA_reflects) else $error("NAND4: A edge not reflected when B=C=D=1");
  assert property (p_edgeB_reflects) else $error("NAND4: B edge not reflected when A=C=D=1");
  assert property (p_edgeC_reflects) else $error("NAND4: C edge not reflected when A=B=D=1");
  assert property (p_edgeD_reflects) else $error("NAND4: D edge not reflected when A=B=C=1");

  // Coverage: key truth-table corners and dynamic behavior
  cover property (p_all1_forces0);
  cover property (@(`ANY_IN_EDGE) (A===0 && B===1 && C===1 && D===1) ##0 (Y===1));
  cover property (@(`ANY_IN_EDGE) (A===1 && B===0 && C===1 && D===1) ##0 (Y===1));
  cover property (@(`ANY_IN_EDGE) (A===1 && B===1 && C===0 && D===1) ##0 (Y===1));
  cover property (@(`ANY_IN_EDGE) (A===1 && B===1 && C===1 && D===0) ##0 (Y===1));
  cover property (@(posedge A) (B===1 && C===1 && D===1) ##0 (Y===~A));
  cover property (@(posedge B) (A===1 && C===1 && D===1) ##0 (Y===~B));
  cover property (@(posedge C) (A===1 && B===1 && D===1) ##0 (Y===~C));
  cover property (@(posedge D) (A===1 && B===1 && C===1) ##0 (Y===~D));
  cover property (@(`ANY_IN_EDGE) ($isunknown({A,B,C,D}) && !((A===0)||(B===0)||(C===0)||(D===0)) && (Y===1'bx)));

  `undef ANY_IN_EDGE
endmodule

// Bind into the DUT
bind sky130_fd_sc_ms__nand4 sky130_fd_sc_ms__nand4_sva nand4_sva_i (.Y(Y), .A(A), .B(B), .C(C), .D(D));