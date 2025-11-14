// SVA for sky130_fd_sc_lp__fahcin
// Bind these assertions to the DUT type
`ifndef SYNTHESIS
bind sky130_fd_sc_lp__fahcin sky130_fd_sc_lp__fahcin_sva u_sky130_fd_sc_lp__fahcin_sva();
`endif

module sky130_fd_sc_lp__fahcin_sva;

  // Inputs/outputs/internal nets are visible in bound scope

  // Power/ground sanity
  assert property (@(*)
    (VPWR === 1'b1) && (VPB === 1'b1) && (VGND === 1'b0) && (VNB === 1'b0));

  // When inputs are known, everything is known
  assert property (@(*)
    !$isunknown({A,B,CIN}) |-> !$isunknown({SUM,COUT,ci,xor0_out_SUM,a_b,a_ci,b_ci,or0_out_COUT}));

  // Golden functionality (full-adder with inverted carry-in)
  assert property (@(*)
    !$isunknown({A,B,CIN}) |-> SUM  === (A ^ B ^ ~CIN));
  assert property (@(*)
    !$isunknown({A,B,CIN}) |-> COUT === ((A & B) | (A & ~CIN) | (B & ~CIN)));
  assert property (@(*)
    !$isunknown({A,B,CIN}) |-> {COUT,SUM} === (A + B + (~CIN)));

  // Equivalent alternative form for COUT
  assert property (@(*)
    !$isunknown({A,B,CIN}) |-> COUT === ((A & B) | ((A | B) & ~CIN)));

  // Internal net consistency with gates
  assert property (@(*)
    ci === ~CIN);
  assert property (@(*)
    xor0_out_SUM === (A ^ B ^ ci));
  assert property (@(*)
    SUM === xor0_out_SUM);
  assert property (@(*)
    a_b  === (A & B));
  assert property (@(*)
    a_ci === (A & ci));
  assert property (@(*)
    b_ci === (B & ci));
  assert property (@(*)
    or0_out_COUT === (a_b | a_ci | b_ci));
  assert property (@(*)
    COUT === or0_out_COUT);

  // Symmetry in A and B
  assert property (@(*)
    !$isunknown({A,B,CIN}) |-> (SUM === (B ^ A ^ ~CIN) &&
                                COUT === ((B & A) | (B & ~CIN) | (A & ~CIN))));

  // Functional coverage: exercise all input combinations
  cover property (@(*) {A,B,CIN} == 3'b000);
  cover property (@(*) {A,B,CIN} == 3'b001);
  cover property (@(*) {A,B,CIN} == 3'b010);
  cover property (@(*) {A,B,CIN} == 3'b011);
  cover property (@(*) {A,B,CIN} == 3'b100);
  cover property (@(*) {A,B,CIN} == 3'b101);
  cover property (@(*) {A,B,CIN} == 3'b110);
  cover property (@(*) {A,B,CIN} == 3'b111);

  // Toggle coverage on outputs
  cover property (@(posedge SUM) 1);
  cover property (@(negedge SUM) 1);
  cover property (@(posedge COUT) 1);
  cover property (@(negedge COUT) 1);

endmodule