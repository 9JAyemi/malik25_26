// SVA for binary_counter
module binary_counter_sva #(parameter int N = 4) (
  input logic              clk,
  input logic              rst,   // active-low async
  input logic [N-1:0]      count
);
  localparam logic [N-1:0] MAX = {N{1'b1}};

  default clocking cb @(posedge clk); endclocking

  // Basic X checks at clock sample
  assert property ( !$isunknown(rst) );
  assert property ( !$isunknown(count) );

  // Async reset clears immediately on negedge (observe after NBAs)
  assert property ( @(negedge rst) ##0 (count == '0) );

  // While reset is asserted at a clock edge, count is 0 (check after NBAs)
  assert property ( !rst |-> ##0 (count == '0) );

  // When out of reset in consecutive cycles, counter increments by 1 (mod 2^N)
  assert property ( rst && $past(rst) |-> ##0 (count == $past(count) + 1) );

  // Optional: while reset is held across consecutive clocks, value holds at 0
  assert property ( !rst && $past(!rst) |-> ##0 (count == $past(count)) );

  // Coverage
  // See an async reset clear
  cover property ( @(negedge rst) ##0 (count == '0) );
  // See a normal increment (any non-reset back-to-back clocks)
  cover property ( rst && $past(rst) ##0 (count == $past(count) + 1) );
  // See rollover from MAX to 0
  cover property ( rst && $past(rst) && ($past(count) == MAX) ##0 (count == '0) );
endmodule

bind binary_counter binary_counter_sva #(.N(N)) i_binary_counter_sva (.*);