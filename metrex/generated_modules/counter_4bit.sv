// SVA for counter_4bit
// Bind this module to the DUT instance/type as shown at the bottom.

module counter_4bit_sva (
  input logic       clk,
  input logic       rst,
  input logic [3:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Track when $past() is valid on the clock
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // 1) No X/Z on sampled output
  a_no_x: assert property ( !$isunknown(count) );

  // 2) Asynchronous reset drives count to 0 immediately at rst posedge
  //    (##0 moves sampling after the DUT's nonblocking updates)
  a_async_immediate_zero: assert property (@(posedge rst) ##0 (! $isunknown(count) && count == 4'h0));

  // 3) While rst is asserted at a clock edge, output must be 0
  a_reset_holds_zero: assert property ( rst |-> count == 4'h0 );

  // 4) If rst stays asserted across consecutive clocks, count remains stable at 0
  a_reset_stable: assert property ( rst && $past(rst) |-> (count == 4'h0 && $stable(count)) );

  // 5) Increment by 1 modulo 16 on every non-reset clock
  a_inc_mod16: assert property (
    disable iff (rst || !past_valid)
    $unsigned(count) == ($unsigned($past(count)) + 1) % 16
  );

  // 6) Explicit rollover: F -> 0 on next non-reset clock
  a_rollover: assert property (
    disable iff (rst || !past_valid)
    ($past(count) == 4'hF) |-> (count == 4'h0)
  );

  // 7) First non-reset cycle after deassertion produces 1 (since reset value is 0)
  a_first_after_reset_is_one: assert property (
    disable iff (!past_valid)
    $past(rst) && !rst |-> count == 4'h1
  );

  // Coverage

  // C1) See a reset followed by deassertion and first count of 1
  c_reset_to_run: cover property ( $rose(rst) ##1 !rst ##1 (count == 4'h1) );

  // C2) See a rollover event
  c_rollover: cover property ( disable iff (rst || !past_valid) ($past(count) == 4'hF && count == 4'h0) );

  // C3) See 16 consecutive valid increments (full-span run without reset)
  sequence s_inc_mod16;
    $unsigned(count) == ($unsigned($past(count)) + 1) % 16;
  endsequence
  c_16_steps: cover property ( disable iff (rst || !past_valid) s_inc_mod16 [*16] );

endmodule

// Bind to the DUT (type bind shown; instance bind also acceptable)
// Ensure this is compiled after the DUT.
bind counter_4bit counter_4bit_sva u_counter_4bit_sva (.clk(clk), .rst(rst), .count(count));