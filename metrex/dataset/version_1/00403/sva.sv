// SVA for four_to_one
// Concise, functionally complete, with key checks and coverage

module four_to_one_sva (
  input logic Y,
  input logic A1, A2, B1, B2,
  input logic VPWR, VGND, VPB, VNB
);

  function automatic logic exp_y (logic A1, A2, B1, B2);
    return ((A1 & A2 & B1 & B2)
          | (A1 & A2 & ~B1 & ~B2)
          | (A1 & ~A2 & B1 & ~B2)
          | (~A1 & A2 & ~B1 & B2));
  endfunction

  // Functional equivalence (combinational, X-safe)
  property p_func;
    @(A1 or A2 or B1 or B2 or Y)
      !$isunknown({A1,A2,B1,B2,VPWR,VGND,VPB,VNB})
      |-> (Y === exp_y(A1,A2,B1,B2));
  endproperty
  assert property (p_func);

  // No X on Y when inputs and rails are known
  property p_no_x_out;
    @(A1 or A2 or B1 or B2 or Y)
      !$isunknown({A1,A2,B1,B2,VPWR,VGND,VPB,VNB})
      |-> !$isunknown(Y);
  endproperty
  assert property (p_no_x_out);

  // Output only changes in response to input change (no spontaneous glitches)
  property p_no_spurious_change;
    @(Y) $changed(Y) |-> $changed({A1,A2,B1,B2});
  endproperty
  assert property (p_no_spurious_change);

  // Rails sanity (must be at legal constants by end of sim)
  assert final (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);

  // Coverage: all four on-minterms
  cover property (@(A1 or A2 or B1 or B2)
    A1 & A2 & B1 & B2 & (Y===1));
  cover property (@(A1 or A2 or B1 or B2)
    A1 & A2 & ~B1 & ~B2 & (Y===1));
  cover property (@(A1 or A2 or B1 or B2)
    A1 & ~A2 & B1 & ~B2 & (Y===1));
  cover property (@(A1 or A2 or B1 or B2)
    ~A1 & A2 & ~B1 & B2 & (Y===1));

  // Coverage: at least a representative off-minterm
  cover property (@(A1 or A2 or B1 or B2)
    ~A1 & ~A2 & ~B1 & ~B2 & (Y===0));

  // Coverage: observe both Y transitions
  cover property (@(A1 or A2 or B1 or B2 or Y) $rose(Y));
  cover property (@(A1 or A2 or B1 or B2 or Y) $fell(Y));

endmodule

// Bind into DUT
bind four_to_one four_to_one_sva sva_i(
  .Y(Y), .A1(A1), .A2(A2), .B1(B1), .B2(B2),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);