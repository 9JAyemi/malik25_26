// SVA checkers and binds for full_adder and four_bit_adder

// Checker for 1-bit full_adder
module full_adder_sva;
  // No X/Z on outputs when inputs are known
  assert property (@(A or B or CIN) (!$isunknown({A,B,CIN})) |-> ##0 (!$isunknown({SUM,COUT})));

  // Functional correctness
  assert property (@(A or B or CIN) ##0 {COUT,SUM} == (A + B + CIN));
  assert property (@(A or B or CIN) ##0 (SUM == (A ^ B ^ CIN)));
  assert property (@(A or B or CIN) ##0 (COUT == ((A & (B | CIN)) | (B & CIN))));

  // Compact functional coverage
  cover property (@(A or B or CIN) (A==0 && B==0 && CIN==0));
  cover property (@(A or B or CIN) (A==1 && B==1 && CIN==1));
  cover property (@(A or B or CIN) ((A^B) && (CIN==0))); // propagate, Cin=0
  cover property (@(A or B or CIN) ((A^B) && (CIN==1))); // propagate, Cin=1
  cover property (@(A or B or CIN) (A&B));               // generate
  cover property (@(A or B or CIN) (~A & ~B));           // kill
endmodule

// Checker for 4-bit ripple adder
module four_bit_adder_sva;
  // No X/Z on outputs when inputs are known
  assert property (@(A or B) (!$isunknown({A,B})) |-> ##0 (!$isunknown(SUM)));

  // Overall arithmetic equivalence
  assert property (@(A or B) ##0 SUM == ({1'b0,A} + {1'b0,B}));
  assert property (@(A or B) ##0 {SUM[4],SUM[3:0]} == (A + B));

  // Ripple-chain detail checks
  let c0 = A[0] & B[0];
  let c1 = (A[1] & (B[1] | c0)) | (B[1] & c0);
  let c2 = (A[2] & (B[2] | c1)) | (B[2] & c1);
  let c3 = (A[3] & (B[3] | c2)) | (B[3] & c2);

  assert property (@(A or B) ##0 (CARRY0 == c0) && (CARRY1 == c1) && (CARRY2 == c2) && (SUM[4] == c3));
  assert property (@(A or B) ##0 (SUM[0] == (A[0] ^ B[0])));            // Cin=0 for bit0
  assert property (@(A or B) ##0 (SUM[1] == (A[1] ^ B[1] ^ CARRY0)));
  assert property (@(A or B) ##0 (SUM[2] == (A[2] ^ B[2] ^ CARRY1)));
  assert property (@(A or B) ##0 (SUM[3] == (A[3] ^ B[3] ^ CARRY2)));

  // Wiring/misconnection sanity checks to the instantiated full_adders
  assert property (@(A or B) ##0 (op1.CIN == 1'b0) && (op2.CIN == CARRY0) && (op3.CIN == CARRY1) && (op4.CIN == CARRY2));
  assert property (@(A or B) ##0 (op1.SUM == SUM[0]) && (op2.SUM == SUM[1]) && (op3.SUM == SUM[2]) && (op4.SUM == SUM[3]) && (op4.COUT == SUM[4]));

  // Compact functional coverage
  cover property (@(A or B) (A==4'h0 && B==4'h0));   // zero+zero
  cover property (@(A or B) (A==4'hF && B==4'hF));   // max+max -> overflow
  cover property (@(A or B) (SUM[4] == 1'b1));       // overflow observed
  cover property (@(A or B) (SUM[4] == 1'b0));       // no overflow
  cover property (@(A or B) (CARRY0==1 && CARRY1==1 && CARRY2==1)); // long carry chain
  cover property (@(A or B) (CARRY0==0 && CARRY1==0 && CARRY2==0)); // no carries
  cover property (@(A or B) CARRY0 == 1);
  cover property (@(A or B) CARRY0 == 0);
  cover property (@(A or B) CARRY1 == 1);
  cover property (@(A or B) CARRY1 == 0);
  cover property (@(A or B) CARRY2 == 1);
  cover property (@(A or B) CARRY2 == 0);
endmodule

// Bind the checkers to all instances
bind full_adder     full_adder_sva     fa_checks();
bind four_bit_adder four_bit_adder_sva fba_checks();