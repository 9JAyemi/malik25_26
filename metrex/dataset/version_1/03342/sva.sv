// SVA for shift_register_4bit
// Bind into the DUT; references internal regs Q1..Q4

module shift_register_4bit_sva;

  default clocking cb @(posedge clk); endclocking

  bit init_done;
  always_ff @(posedge clk) if (load) init_done <= 1'b1;

  // Structural width sanity: concat is 16b, Q is 4b -> flag mismatch
  initial begin
    if ($bits(Q) != $bits({Q4,Q3,Q2,Q1}))
      $error("Width mismatch: Q is %0d bits, concat is %0d bits",
             $bits(Q), $bits({Q4,Q3,Q2,Q1}));
  end

  // During load, capture A..D into Q1..Q4 on next cycle
  assert property (load |=> (Q1==$past(A) && Q2==$past(B) && Q3==$past(C) && Q4==$past(D)))
    else $error("Load failed: Q1..Q4 did not capture A..D");

  // During shift (load=0), rotate: Q1<-Q2, Q2<-Q3, Q3<-Q4, Q4<-Q
  assert property (!load |=> (Q1==$past(Q2) && Q2==$past(Q3) && Q3==$past(Q4) && Q4==$past(Q)))
    else $error("Shift/rotate failed");

  // Due to assign truncation, Q is effectively Q1; catch unintended mapping
  assert property (init_done |-> (Q == Q1))
    else $error("Q does not reflect Q1 as implied by current assign");

  // 4-cycle periodicity under continuous shifting
  sequence four_shifts; !load[*4]; endsequence
  assert property (init_done && four_shifts |=> (Q1==$past(Q1,4) && Q2==$past(Q2,4)
                                               && Q3==$past(Q3,4) && Q4==$past(Q4,4)
                                               && Q  ==$past(Q,4)))
    else $error("State not periodic over 4 shifts");

  // X/Z sanitation
  assert property (load |-> !$isunknown({A,B,C,D}))
    else $error("X/Z on inputs during load");
  assert property (init_done && !load |-> !$isunknown({Q1,Q2,Q3,Q4,Q}))
    else $error("X/Z detected in state during shift");

  // Minimal coverage
  cover property (load);
  cover property (!load);
  cover property (load ##1 !load[*4]);        // load then 4 shifts
  cover property (init_done && four_shifts);  // rotation activity

endmodule

bind shift_register_4bit shift_register_4bit_sva sva_i;