// SVA for d_ff_async_reset
module d_ff_async_reset_sva(input logic D, RESET_B, CLK, Q, Q_N);

  // Complement consistency (also flags X/Z via ===)
  assert property (@(posedge CLK or posedge RESET_B or negedge RESET_B)
                   ##0 (Q_N === ~Q));

  // Async reset takes effect immediately
  assert property (@(negedge RESET_B) ##0 (Q == 1'b0 && Q_N == 1'b1));

  // While in reset, outputs remain forced (including at clock edges)
  assert property (@(posedge CLK) !RESET_B |-> ##0 (Q == 1'b0 && Q_N == 1'b1));

  // First clock after reset release captures current D
  assert property (@(posedge CLK) $rose(RESET_B) |-> ##0 (Q == D));

  // Normal operation: sample previous D on each clock
  assert property (@(posedge CLK) (RESET_B && $past(RESET_B)) |-> ##0 (Q == $past(D)));

  // No unknowns when reset is known
  assert property (@(posedge CLK or posedge RESET_B or negedge RESET_B)
                   !$isunknown(RESET_B) |-> ##0 !$isunknown({Q,Q_N}));

  // Coverage
  cover property (@(negedge RESET_B));
  cover property (@(posedge CLK) $rose(RESET_B));
  cover property (@(posedge CLK) RESET_B && $past(RESET_B) && ($past(D)==1) ##0 (Q==1));
  cover property (@(posedge CLK) RESET_B && $past(RESET_B) && ($past(D)==0) ##0 (Q==0));
  cover property (@(posedge CLK) RESET_B && $past(RESET_B) && $changed(Q));

endmodule

bind d_ff_async_reset d_ff_async_reset_sva sva_inst (.*);