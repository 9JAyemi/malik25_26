// SVA for ripple_adder
// Bind into the DUT to check functionality and internal stage equations

bind ripple_adder ripple_adder_sva();

module ripple_adder_sva;

  function automatic bit known_inputs();
    return !$isunknown({A,B,CIN});
  endfunction

  // End-to-end correctness (primary check)
  a_full_correct: assert property (@(*) disable iff (!known_inputs())
                                   {COUT,SUM} == A + B + CIN)
    else $error("Adder mismatch: A=%0h B=%0h CIN=%0b -> SUM=%0h COUT=%0b", A, B, CIN, SUM, COUT);

  // No X on outputs when inputs are known
  a_no_x_out: assert property (@(*) known_inputs() |-> ##0 !$isunknown({SUM,COUT}));

  // Stage 1 (bit0) equations
  a_s1_sum0:  assert property (@(*) disable iff (!known_inputs())
                               stage1_SUM[0] == (A[0]^B[0]^CIN));
  a_s1_cout:  assert property (@(*) disable iff (!known_inputs())
                               stage1_COUT   == ((A[0]&B[0])|(A[0]&CIN)|(B[0]&CIN)));

  // Stage 2 (bit1) equations
  a_s2_sum1:  assert property (@(*) disable iff (!known_inputs())
                               stage2_SUM[1] == (A[1]^B[1]^stage1_COUT));
  a_s2_cout:  assert property (@(*) disable iff (!known_inputs())
                               stage2_COUT   == ((A[1]&B[1])|(A[1]&stage1_COUT)|(B[1]&stage1_COUT)));

  // Stage 3 (bit2) equations and carry into bit3 (named COUT in DUT)
  a_s3_sum2:  assert property (@(*) disable iff (!known_inputs())
                               stage3_SUM[2] == (A[2]^B[2]^stage2_COUT));
  a_carry_in_bit3: assert property (@(*) disable iff (!known_inputs())
                                    COUT == ((A[2]&B[2])|(A[2]&stage2_COUT)|(B[2]&stage2_COUT)));

  // Stage 4 (bit3) sum uses carry into bit3
  a_s4_sum3:  assert property (@(*) disable iff (!known_inputs())
                               stage3_SUM[3] == (A[3]^B[3]^COUT));

  // Output connectivity to stage sums
  a_sum0_conn: assert property (@(*) disable iff (!known_inputs())
                                SUM[0] == stage1_SUM[0]);
  a_sum1_conn: assert property (@(*) disable iff (!known_inputs())
                                SUM[1] == stage2_SUM[1]);
  a_sum2_conn: assert property (@(*) disable iff (!known_inputs())
                                SUM[2] == stage3_SUM[2]);
  a_sum3_conn: assert property (@(*) disable iff (!known_inputs())
                                SUM[3] == stage3_SUM[3]);

  // Coverage: key scenarios
  c_no_carry:      cover property (@(*) known_inputs() && (COUT==1'b0) && ({COUT,SUM} == A + B + CIN));
  c_overflow:      cover property (@(*) known_inputs() && (COUT==1'b1) && ({COUT,SUM} == A + B + CIN));
  c_full_propagate:cover property (@(*) known_inputs() && ((A^B)==4'hF) && ((A&B)==4'h0) && (CIN==1'b1));
  c_gen_b0:        cover property (@(*) known_inputs() && A[0] && B[0]);
  c_gen_b3:        cover property (@(*) known_inputs() && A[3] && B[3]);

endmodule