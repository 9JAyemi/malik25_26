// SVA for top_module
module top_module_sva;

  default clocking cb @(posedge CLK); endclocking

  // Reset behavior
  assert property (@cb RESET |-> (count==4'h0 && parity_bit==1'b0 && Q==4'h0));

  // Count next-state (with wrap)
  assert property (@cb disable iff (RESET)
                   $past(!RESET) && UP_DOWN && $past(count)!=4'hF |-> count == $past(count)+1);
  assert property (@cb disable iff (RESET)
                   $past(!RESET) && UP_DOWN && $past(count)==4'hF |-> count == 4'h0);
  assert property (@cb disable iff (RESET)
                   $past(!RESET) && !UP_DOWN && $past(count)!=4'h0 |-> count == $past(count)-1);
  assert property (@cb disable iff (RESET)
                   $past(!RESET) && !UP_DOWN && $past(count)==4'h0 |-> count == 4'hF);

  // Parity updates from previous count; parity output mirrors register
  assert property (@cb disable iff (RESET)
                   $past(!RESET) |-> parity_bit == ^$past(count));
  assert property (@cb parity == parity_bit);

  // Q update path
  assert property (@cb disable iff (RESET)
                   $past(!RESET) && SELECT |-> Q == $past(count));
  assert property (@cb disable iff (RESET)
                   $past(!RESET) && !SELECT |-> Q == {3'b000, $past(parity_bit)});

  // No X/Z on state/outputs after reset release
  assert property (@cb disable iff (RESET)
                   !$isunknown({count, parity_bit, Q, parity}));

  // Coverage
  cover property (@cb RESET ##1 !RESET);
  cover property (@cb disable iff (RESET) $past(!RESET) && UP_DOWN && $past(count)!=4'hF);
  cover property (@cb disable iff (RESET) $past(!RESET) && UP_DOWN && $past(count)==4'hF);
  cover property (@cb disable iff (RESET) $past(!RESET) && !UP_DOWN && $past(count)!=4'h0);
  cover property (@cb disable iff (RESET) $past(!RESET) && !UP_DOWN && $past(count)==4'h0);
  cover property (@cb disable iff (RESET) $past(!RESET) && SELECT);
  cover property (@cb disable iff (RESET) $past(!RESET) && !SELECT);

endmodule

bind top_module top_module_sva sva_top_module();