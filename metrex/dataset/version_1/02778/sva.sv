// SVA for bitwise_module
// Bind into the DUT to check internal nets and provide concise yet thorough coverage

module bitwise_module_assertions (
  input logic A1, A2, A3, B1,
  input logic VPWR, VGND, VPB, VNB,
  input logic out,
  // internal nets
  input logic and1, and2, or1, xor1, or2
);

  // Functional equivalence under known inputs
  property p_func_eq;
    @(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB)
      !$isunknown({A1,A2,A3,B1,VPWR,VGND,VPB,VNB})
      |-> out === (((A1 & A2) | (A3 & B1)) & (VPWR ^ VGND) & (VPB | VNB));
  endproperty
  assert property (p_func_eq);

  // Gate-by-gate local consistency (checks all internal functions)
  assert property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) and1 === (A1 & A2));
  assert property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) and2 === (A3 & B1));
  assert property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) or1  === (and1 | and2));
  assert property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) xor1 === (VPWR ^ VGND));
  assert property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) or2  === (VPB | VNB));
  assert property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) out  === (or1 & xor1 & or2));

  // X-safety: when inputs are known, no X/Z on internal nets or output
  assert property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB)
                   !$isunknown({A1,A2,A3,B1,VPWR,VGND,VPB,VNB})
                   |-> !$isunknown({and1,and2,or1,xor1,or2,out}));

  // Gating behavior corner checks
  // If power xor gate is 0 (VPWR == VGND, both known), out must be 0 regardless of others
  assert property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB)
                   (!$isunknown({VPWR,VGND}) && (VPWR === VGND)) |-> (out === 1'b0));
  // If bulk OR gate is 0 (VPB==0 && VNB==0, both known), out must be 0 regardless of others
  assert property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB)
                   (!$isunknown({VPB,VNB}) && (VPB===1'b0) && (VNB===1'b0)) |-> (out === 1'b0));
  // Nominal supplies: VPWR=1, VGND=0, VPB=1, VNB=0 -> out mirrors or1
  assert property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB)
                   (!$isunknown({VPWR,VGND,VPB,VNB}) && VPWR && !VGND && VPB && !VNB)
                   |-> (out === or1));

  // Minimal functional coverage: drive each internal function to 0 and 1, and out to 0 and 1
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) and1 == 1);
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) and1 == 0);
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) and2 == 1);
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) and2 == 0);
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) or1  == 1);
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) or1  == 0);
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) xor1 == 1);
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) xor1 == 0);
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) or2  == 1);
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) or2  == 0);
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) out  == 1);
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) out  == 0);

  // Stimulus-interest coverage: which product terms drive or1
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) (and1 && !and2));
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) (and2 && !and1));
  cover property (@(A1 or A2 or A3 or B1 or VPWR or VGND or VPB or VNB) (and1 && and2));

endmodule

// Bind into every instance of bitwise_module
bind bitwise_module bitwise_module_assertions sva (
  .A1(A1), .A2(A2), .A3(A3), .B1(B1),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
  .out(out),
  .and1(and1), .and2(and2), .or1(or1), .xor1(xor1), .or2(or2)
);