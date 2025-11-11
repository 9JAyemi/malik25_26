// Bind these SVA to the DUT
bind pipelined_JC_counter pipelined_JC_counter_sva sva();

module pipelined_JC_counter_sva;

  // Access bound instance scope: clk, rst_n, Q, Q1..Q16
  default clocking cb @(posedge clk); endclocking

  // Reset behavior: pipeline regs clear, Q holds its value during reset
  assert property (@(posedge clk)
    !rst_n |-> (Q1=='0 && Q2=='0 && Q3=='0 && Q4=='0 && Q5=='0 && Q6=='0 && Q7=='0 && Q8=='0 &&
                Q9=='0 && Q10=='0 && Q11=='0 && Q12=='0 && Q13=='0 && Q14=='0 && Q15=='0 && Q16=='0 &&
                $stable(Q))
  );

  // First cycle after reset release, Q must be 0 (since Q16 was 0 in reset)
  assert property (@(posedge clk) $rose(rst_n) |-> (Q=='0));

  // No X/Z out of reset
  assert property (@(posedge clk) rst_n |-> !$isunknown({Q,Q1,Q2,Q3,Q4,Q5,Q6,Q7,Q8,Q9,Q10,Q11,Q12,Q13,Q14,Q15,Q16}));

  // One-cycle pipeline relation: pass upper bits, toggle LSB via ^ 16'h0001
  assert property (rst_n |->
    {Q1,Q2,Q3,Q4,Q5,Q6,Q7,Q8,Q9,Q10,Q11,Q12,Q13,Q14,Q15,Q16} ==
    {$past(Q16)^16'h0001,
     $past(Q1)^16'h0001,  $past(Q2)^16'h0001,  $past(Q3)^16'h0001,  $past(Q4)^16'h0001,
     $past(Q5)^16'h0001,  $past(Q6)^16'h0001,  $past(Q7)^16'h0001,  $past(Q8)^16'h0001,
     $past(Q9)^16'h0001,  $past(Q10)^16'h0001, $past(Q11)^16'h0001, $past(Q12)^16'h0001,
     $past(Q13)^16'h0001, $past(Q14)^16'h0001, $past(Q15)^16'h0001}
  );

  // Output latency: Q reflects prior Q16
  assert property (rst_n |-> (Q == $past(Q16)));

  // Ring equality invariant out of reset (proves pipeline stays phase-aligned)
  assert property (rst_n |-> (Q1==Q2 && Q2==Q3 && Q3==Q4 && Q4==Q5 && Q5==Q6 && Q6==Q7 && Q7==Q8 &&
                              Q8==Q9 && Q9==Q10 && Q10==Q11 && Q11==Q12 && Q12==Q13 &&
                              Q13==Q14 && Q14==Q15 && Q15==Q16));

  // Coverage
  cover property (@(posedge clk) $rose(rst_n));
  cover property (@(posedge clk) rst_n && Q==16'h0000 ##1 rst_n && Q==16'h0001 ##1 rst_n && Q==16'h0000);
  cover property (@(posedge clk) rst_n && (Q1==Q2) && (Q2==Q3) && (Q15==Q16));

endmodule