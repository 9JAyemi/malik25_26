// SVA for counter_4bit
module counter_4bit_sva (
  input logic       clk,
  input logic       rst,
  input logic [3:0] count
);
  // Track valid past sample to avoid t=0 $past issues
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Basic sanity: no X/Z on count at clock sample
  assert property ( !$isunknown(count) );

  // Asynchronous reset drives count to 0 immediately (NBA) on rst rise
  assert property ( @(posedge rst) ##0 (count == 4'h0) );

  // Reset dominates at clock edge
  assert property ( rst |-> (count == 4'h0) );

  // Increment by 1 modulo 16 when not in reset
  assert property ( disable iff (rst || !past_valid)
                    count == (($past(count) + 4'h1) & 4'hF) );

  // Explicit wrap check: F -> 0 on next clk when not in reset
  assert property ( disable iff (rst || !past_valid)
                    ($past(count) == 4'hF) |-> (count == 4'h0) );

  // Coverage
  cover property ( @(posedge rst) 1 ); // saw async reset edge
  cover property ( rst );              // saw reset high on a clk edge
  cover property ( disable iff (rst || !past_valid)
                   ($past(count) == 4'h7) && (count == 4'h8) ); // normal increment
  cover property ( disable iff (rst || !past_valid)
                   ($past(count) == 4'hF) && (count == 4'h0) ); // wrap-around
endmodule

// Bind into DUT
bind counter_4bit counter_4bit_sva u_counter_4bit_sva (.*);