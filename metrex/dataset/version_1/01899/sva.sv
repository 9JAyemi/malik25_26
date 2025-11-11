// SVA for dff_async_reset_enable
module dff_async_reset_enable_sva (
  input logic CLK,
  input logic D,
  input logic RESET,
  input logic EN,
  input logic Q,
  input logic Q_N
);

  // Asynchronous reset sets outputs immediately
  assert property (@(negedge RESET) 1 |-> (Q === 1'b0 && Q_N === 1'b1));

  // While reset is asserted, outputs must stay in reset state
  assert property (@(posedge CLK) (!RESET) |-> (Q === 1'b0 && Q_N === 1'b1));

  // Q_N is always the complement of Q (check on both controlling events)
  assert property (@(posedge CLK or negedge RESET) 1 |-> (Q_N === ~Q));

  // Hold behavior when disabled (guard first valid past with $past(RESET))
  assert property (@(posedge CLK) disable iff (!RESET)
                   (!EN && $past(RESET)) |=> $stable({Q, Q_N}));

  // Capture behavior when enabled (and D is known), using previous-cycle D
  assert property (@(posedge CLK) disable iff (!RESET)
                   (EN && !$isunknown(D) && $past(RESET)) |=> (Q === $past(D) && Q_N === ~$past(D)));

  // Functional coverage
  // Reset assertion observed
  cover property (@(negedge RESET) 1);

  // Capture D=0 and D=1 when enabled
  cover property (@(posedge CLK) disable iff (!RESET)
                  (EN && !$isunknown(D) && $past(RESET) && $past(D) == 1'b0) |=> (Q == 1'b0 && Q_N == 1'b1));
  cover property (@(posedge CLK) disable iff (!RESET)
                  (EN && !$isunknown(D) && $past(RESET) && $past(D) == 1'b1) |=> (Q == 1'b1 && Q_N == 1'b0));

  // Hold for two consecutive disabled cycles
  cover property (@(posedge CLK) disable iff (!RESET)
                  (!EN && $past(RESET)) ##1 (!EN) ##1 $stable({Q, Q_N}));

endmodule

bind dff_async_reset_enable dff_async_reset_enable_sva sva_inst (.*);