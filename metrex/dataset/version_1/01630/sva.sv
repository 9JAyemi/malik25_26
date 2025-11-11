// SVA checker for add8
module add8_sva (add8 dut);

  // Expected 9-bit result (models true carry-in behavior)
  let exp9 = {1'b0, dut.A} + {1'b0, dut.B} + dut.signed_unsigned;

  // Functional correctness with zero-latency response
  assert property (@(dut.A or dut.B or dut.signed_unsigned)
                   1'b1 |-> ##0 {dut.carry_out, dut.sum} == exp9);

  // Bit-level consistency (helps localize failures)
  assert property (@(dut.A or dut.B or dut.signed_unsigned)
                   1'b1 |-> ##0 dut.carry_out == exp9[8]);
  assert property (@(dut.A or dut.B or dut.signed_unsigned)
                   1'b1 |-> ##0 dut.sum == exp9[7:0]);

  // Outputs known iff inputs known
  assert property (@(dut.A or dut.B or dut.signed_unsigned or dut.sum or dut.carry_out)
                   !$isunknown({dut.A, dut.B, dut.signed_unsigned}) |-> ##0
                   !$isunknown({dut.sum, dut.carry_out}));

  // Outputs only change when inputs change
  assert property (@(dut.A or dut.B or dut.signed_unsigned or dut.sum or dut.carry_out)
                   ($changed(dut.sum) || $changed(dut.carry_out)) |->
                   ($changed(dut.A) || $changed(dut.B) || $changed(dut.signed_unsigned)));

  // Coverage
  cover property (@(dut.A or dut.B or dut.signed_unsigned) exp9[8]);                          // carry asserted
  cover property (@(dut.A or dut.B or dut.signed_unsigned) !exp9[8]);                         // no carry
  cover property (@(dut.A or dut.B or dut.signed_unsigned) exp9 == 9'h100);                   // wrap exactly 256
  cover property (@(dut.A or dut.B or dut.signed_unsigned) (dut.A==8'h00 && dut.B==8'h00 &&
                                                            dut.signed_unsigned==1'b0));      // zero + zero
endmodule

bind add8 add8_sva u_add8_sva();