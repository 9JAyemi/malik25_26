// SVA for ripple_carry_adder
// Bind into the DUT to see internal nets
module rca_sva;
  // Functional correctness (observed after NBAs settle)
  property p_func; @(A or B or CIN) 1 |-> {COUT, SUM} == A + B + CIN; endproperty
  a_func: assert property (p_func);

  // Registered inputs must track inputs on the triggering event
  property p_regs_track; @(A or B or CIN) 1 |-> (A_reg==A && B_reg==B && CIN_reg==CIN); endproperty
  a_regs_track: assert property (p_regs_track);

  // Stage-wise correctness of ripple chain
  property p_s0; @(A or B or CIN) 1 |-> {COUT1, SUM1[0]} == A_reg[0] + B_reg[0] + CIN_reg; endproperty
  property p_s1; @(A or B or CIN) 1 |-> {COUT2, SUM2[1]} == A_reg[1] + B_reg[1] + COUT1;  endproperty
  property p_s2; @(A or B or CIN) 1 |-> {COUT3, SUM3[2]} == A_reg[2] + B_reg[2] + COUT2;  endproperty
  property p_s3; @(A or B or CIN) 1 |-> {COUT,  SUM[3]} == A_reg[3] + B_reg[3] + COUT3;  endproperty
  a_s0: assert property(p_s0);
  a_s1: assert property(p_s1);
  a_s2: assert property(p_s2);
  a_s3: assert property(p_s3);

  // Wiring of sum bits
  a_w0: assert property(@(A or B or CIN) SUM[0] == SUM1[0]);
  a_w1: assert property(@(A or B or CIN) SUM[1] == SUM2[1]);
  a_w2: assert property(@(A or B or CIN) SUM[2] == SUM3[2]);

  // No X/Z on outputs when inputs are known
  a_no_x_out: assert property (@(A or B or CIN) !$isunknown({A,B,CIN}) |-> !$isunknown({SUM,COUT}));
  // Internal nets also clean when inputs known
  a_no_x_int: assert property (@(A or B or CIN)
                               !$isunknown({A,B,CIN}) |->
                               (!$isunknown({A_reg,B_reg,CIN_reg}) &&
                                !$isunknown({SUM1[0],SUM2[1],SUM3[2],SUM[3]}) &&
                                !$isunknown({COUT1,COUT2,COUT3,COUT})));

  // Functional coverage
  c_any:      cover property (@(A or B or CIN) {COUT,SUM} == A + B + CIN);
  c_zero:     cover property (@(A or B or CIN) SUM==4'h0 && COUT==1'b0);
  c_max_nco:  cover property (@(A or B or CIN) SUM==4'hF && COUT==1'b0);
  c_overflow: cover property (@(A or B or CIN) SUM==4'h0 && COUT==1'b1);
  c_cout:     cover property (@(A or B or CIN) COUT==1'b1);

  // Propagate-all chain with incoming carry rippling out
  c_all_prop_ripple: cover property (@(A or B or CIN) ((A^B)==4'hF && CIN==1'b1 && COUT==1'b1));

  // Carry kill at each stage (carry set then killed next)
  c_kill1: cover property (@(A or B or CIN) COUT1 && !COUT2);
  c_kill2: cover property (@(A or B or CIN) COUT2 && !COUT3);
  c_kill3: cover property (@(A or B or CIN) COUT3 && !COUT);

  // Carry generation at each stage with no incoming carry to that stage
  c_gen1: cover property (@(A or B or CIN) (A_reg[0]&B_reg[0]) && CIN_reg==0 && COUT1);
  c_gen2: cover property (@(A or B or CIN) (A_reg[1]&B_reg[1]) && COUT1==0 && COUT2);
  c_gen3: cover property (@(A or B or CIN) (A_reg[2]&B_reg[2]) && COUT2==0 && COUT3);
  c_gen4: cover property (@(A or B or CIN) (A_reg[3]&B_reg[3]) && COUT3==0 && COUT);
endmodule

bind ripple_carry_adder rca_sva rca_sva_i();