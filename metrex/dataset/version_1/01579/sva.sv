// SVA for pipelined_JC_counter
module pipelined_JC_counter_sva
(
  input logic              clk,
  input logic              rst_n,
  input logic [3:0]        Q,
  input logic [3:0]        Q1, Q2, Q3, Q4
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (cb !rst_n |-> (Q==4'h0 && Q1==4'h0 && Q2==4'h0 && Q3==4'h0 && Q4==4'h0));

  // No X/Z after reset is stably deasserted
  assert property (cb rst_n && $past(rst_n) |-> !$isunknown({Q,Q1,Q2,Q3,Q4}));

  // Pipeline delays
  assert property (cb rst_n && $past(rst_n) |-> Q1 == $past(Q));
  assert property (cb rst_n && $past(rst_n) |-> Q2 == $past(Q1));
  assert property (cb rst_n && $past(rst_n) |-> Q3 == $past(Q2));
  assert property (cb rst_n && $past(rst_n) |-> Q4 == $past(Q3));

  // Next-state function (uses prior-cycle pipeline regs)
  assert property (cb rst_n && $past(rst_n)
                   |-> Q == ~($past(Q1) ^ $past(Q2) ^ $past(Q3) ^ $past(Q4)));

  // Cross-check using only Q after pipeline warm-up
  assert property (cb rst_n && $past(rst_n,5)
                   |-> Q == ~($past(Q,2) ^ $past(Q,3) ^ $past(Q,4) ^ $past(Q,5)));

  // Held reset keeps registers at 0 (no glitches observed at clock)
  assert property (cb !rst_n && $past(!rst_n)
                   |-> {Q,Q1,Q2,Q3,Q4} == $past({Q,Q1,Q2,Q3,Q4}) && {Q,Q1,Q2,Q3,Q4}==20'h0);

  // Coverage: basic post-reset behavior and pipeline fill
  cover property (cb $rose(rst_n) ##1 (Q==4'hF) ##1 (Q==4'hF) ##1 (Q==4'h0));
  cover property (cb $rose(rst_n)
                  ##[1:8] (Q1!=4'h0)
                  ##[1:8] (Q2!=4'h0)
                  ##[1:8] (Q3!=4'h0)
                  ##[1:8] (Q4!=4'h0));

endmodule

bind pipelined_JC_counter pipelined_JC_counter_sva sva_i(
  .clk(clk),
  .rst_n(rst_n),
  .Q(Q),
  .Q1(Q1),
  .Q2(Q2),
  .Q3(Q3),
  .Q4(Q4)
);