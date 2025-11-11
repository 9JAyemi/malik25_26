// SVA for maj3_2 and maj3
// Concise, bindable, full functional checks and key coverage

// Checker for the wrapper (maj3_2)
module maj3_2_chk (
  input A, input B, input C,
  input VPWR, input VGND, input VPB, input VNB,
  input X,
  input majority // bind to internal net
);
  wire power_good = (VPWR===1'b1) && (VGND===1'b0);

  default clocking cb @($global_clock); endclocking
  default disable iff (!power_good);

  // Power/ground body ties must be correct when powered
  assert property (VPB===VPWR && VNB===VGND);

  // No X/Z on functional signals when powered
  assert property (!$isunknown({A,B,C,X}));

  // Wrapper must pass through base majority result
  assert property (X === majority);

  // X must be functionally stable if inputs are stable
  assert property ($stable({A,B,C}) |-> $stable(X));

  // Functional end-to-end check (redundant but robust)
  assert property (X === ((A & B) | (A & C) | (B & C)));

  // Functional coverage: all input combinations under power-good
  cover property ({A,B,C}==3'b000 && X==1'b0);
  cover property ({A,B,C}==3'b001 && X==1'b0);
  cover property ({A,B,C}==3'b010 && X==1'b0);
  cover property ({A,B,C}==3'b011 && X==1'b1);
  cover property ({A,B,C}==3'b100 && X==1'b0);
  cover property ({A,B,C}==3'b101 && X==1'b1);
  cover property ({A,B,C}==3'b110 && X==1'b1);
  cover property ({A,B,C}==3'b111 && X==1'b1);

  // Output transition coverage
  cover property ($rose(X));
  cover property ($fell(X));
endmodule

// Checker for the base majority cell (maj3)
module maj3_chk (
  input A, input B, input C,
  input VPWR, input VGND,
  input X
);
  wire power_good = (VPWR===1'b1) && (VGND===1'b0);

  default clocking cb @($global_clock); endclocking
  default disable iff (!power_good);

  // No X/Z on functional signals when powered
  assert property (!$isunknown({A,B,C,X}));

  // Majority function correctness
  assert property (X === ((A & B) | (A & C) | (B & C)));

  // Basic coverage (sanity)
  cover property ({A,B,C}==3'b011 && X==1'b1);
  cover property ({A,B,C}==3'b100 && X==1'b0);
endmodule

// Bind the checkers to the DUTs
bind maj3_2 maj3_2_chk m2_chk (
  .A(A), .B(B), .C(C),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
  .X(X),
  .majority(majority)
);

bind maj3 maj3_chk m_chk (
  .A(A), .B(B), .C(C),
  .VPWR(VPWR), .VGND(VGND),
  .X(X)
);