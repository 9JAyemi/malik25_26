// SVA checker for both synchronizer modules
module sync_chain_sva #(parameter int N = 2)
(
  input  logic clk,
  input  logic rst,
  input  logic in,
  input  logic [N-1:0] sync_reg,
  input  logic out
);

  default clocking cb @(posedge clk); endclocking

  // Parameter sanity
  initial assert (N >= 2)
    else $error("Synchronizer length N must be >= 2 for valid shift operation.");

  // While reset is asserted at a sampled clock, state/output are cleared
  assert property (rst |-> (sync_reg == '0 && out == 1'b0));

  // Known values out of reset
  assert property (!rst |-> (!$isunknown(sync_reg) && !$isunknown(out)));

  // Core shift behavior on reset-free cycles (current and previous)
  assert property ((!rst && !$past(rst)) |-> (
                    sync_reg[N-1:1] == $past(sync_reg[N-2:0]) &&
                    sync_reg[0]     == $past(in)));

  // Output is previous-cycle MSB of the chain on reset-free cycles
  assert property ((!rst && !$past(rst)) |-> out == $past(sync_reg[N-1]));

  // After a reset deassertion edge, out must stay 0 for N cycles (pipeline refill)
  assert property ($fell(rst) |-> (out == 1'b0)[*N]);

  // Simple safety: output only changes on clock edges (no X/glitch at sample points)
  assert property (!rst |-> !$isunknown(out));

  // Coverage: show that a clean 0->1 and 1->0 on input propagates after N cycles without reset
  sequence clean_win; !rst [* (N+1)]; endsequence
  cover property (clean_win and $rose(in) ##N $rose(out));
  cover property (clean_win and $fell(in) ##N $fell(out));

endmodule

// Bind the checker to both DUTs (reuses DUT parameter n)
bind ASYNC_TO_SYNC  sync_chain_sva #(.N(n)) u_async_to_sync_sva  (.clk(clk), .rst(rst), .in(in), .sync_reg(sync_reg), .out(out));
bind SYNC_TO_ASYNC  sync_chain_sva #(.N(n)) u_sync_to_async_sva  (.clk(clk), .rst(rst), .in(in), .sync_reg(sync_reg), .out(out));