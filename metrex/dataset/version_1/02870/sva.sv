// SVA checker for counter_4bit
module counter_4bit_sva (
  input logic        clk,
  input logic        reset,   // active-low async reset
  input logic        enable,
  input logic [3:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // Async reset must clear immediately on negedge reset
  assert property (@(negedge reset) ##0 (count == 4'd0))
    else $error("counter_4bit: count not cleared immediately on async reset");

  // While in reset, count must be 0 and stable at clock edges
  assert property ( !reset |-> (count == 4'd0 && $stable(count)) )
    else $error("counter_4bit: count nonzero or changing while reset low");

  // When enabled, count increments by 1 modulo 16
  assert property ( disable iff (!reset)
                    enable |=> count == (($past(count) + 4'd1) % 16) )
    else $error("counter_4bit: bad increment when enable=1");

  // When not enabled, count holds its value
  assert property ( disable iff (!reset)
                    !enable |=> count == $past(count) )
    else $error("counter_4bit: count changed while enable=0");

  // No X/Z on count when out of reset
  assert property ( reset |-> !$isunknown(count) )
    else $error("counter_4bit: count has X/Z when reset=1");

  // Coverage
  cover property (@(negedge reset)); // observe async reset assertion
  cover property ( reset ##1 enable ); // observe first increment opportunity after coming out of reset
  cover property ( disable iff(!reset) (count==4'hF && enable) |=> count==4'h0 ); // wrap 15->0
  cover property ( disable iff(!reset) !enable ##1 enable ##1 !enable ); // hold-inc-hold pattern
  cover property ( disable iff(!reset) enable [*4] ); // burst of 4 increments

endmodule

bind counter_4bit counter_4bit_sva u_counter_4bit_sva (.clk(clk), .reset(reset), .enable(enable), .count(count));