// SVA for binary_counter
// Bind this module to the DUT to verify behavior and cover key scenarios.

module binary_counter_sva #(parameter int W = 4)
(
  input logic              clk,
  input logic              rst,
  input logic              en,
  input logic [W-1:0]      count,
  input logic              carry_out
);

  default clocking cb @(posedge clk); endclocking

  // past-valid guard for $past() usage
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Helpers
  localparam logic [W-1:0] ONE = {{(W-1){1'b0}}, 1'b1};
  localparam logic [W-1:0] MAX = {W{1'b1}};
  localparam logic [W-1:0] ZERO = '0;

  // Reset behavior: synchronous clear to 0
  assert property (rst |=> count == ZERO)
    else $error("Count not cleared to 0 on reset");

  // If reset stays asserted, count stays 0
  assert property (past_valid && $past(rst) && rst |-> count == ZERO && $stable(count))
    else $error("Count not held at 0 during continuous reset");

  // Hold when disabled
  assert property (past_valid && !rst && !en |=> count == $past(count))
    else $error("Count changed while en=0");

  // Increment when enabled (mod-2^W)
  assert property (past_valid && !rst && en |=> count == ($past(count) + ONE))
    else $error("Count did not increment when en=1");

  // Explicit wrap check from MAX -> 0 when enabled
  assert property (past_valid && !rst && $past(en) && $past(count)==MAX |-> count==ZERO)
    else $error("Count failed to wrap from MAX to 0");

  // Carry-out matches MSB wrap indicator (combinational consistency checked on clock)
  assert property (carry_out == (count == MAX))
    else $error("carry_out mismatches count==MAX");

  // No X/Z on key outputs once out of reset
  assert property (past_valid && !rst |-> !$isunknown(count) && !$isunknown(carry_out))
    else $error("Unknown (X/Z) detected on outputs");

  // Coverage

  // See a reset clearing sequence
  cover property (rst ##1 count == ZERO);

  // See an increment step
  cover property (past_valid && !rst && en ##1 count == $past(count) + ONE);

  // See a wrap event F->0 with enable
  cover property (past_valid && !rst && en && count == MAX ##1 count == ZERO);

  // See a 16-cycle enabled run starting at 0 and returning to 0 (full cycle)
  cover property (past_valid && !rst && count==ZERO ##1 (en && !rst)[*16] ##1 count==ZERO);

  // See a hold (no change) while disabled for two cycles
  cover property (past_valid && !rst && !en ##1 count==$past(count) ##1 !en && count==$past(count));

endmodule

// Bind to all instances of binary_counter (carry_out is internal; bind connects hierarchically)
bind binary_counter binary_counter_sva #(.W(4)) binary_counter_sva_i (
  .clk(clk),
  .rst(rst),
  .en(en),
  .count(count),
  .carry_out(carry_out)
);