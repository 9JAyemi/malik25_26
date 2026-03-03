// SVA for up_counter
module up_counter_sva (input clk, input reset, input [3:0] count);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (!reset |-> count == 4'd0)
    else $error("count not 0 during reset");

  // No X/Z out of reset
  assert property (reset |-> !$isunknown(count))
    else $error("count X/Z when out of reset");

  // Increment by exactly +1 when reset is stably high
  assert property (reset && $past(reset) |-> count == $past(count) + 4'd1)
    else $error("count failed to increment by 1");

  // First cycle after reset deassertion
  assert property ($rose(reset) |-> $past(count) == 4'd0 && count == 4'd1)
    else $error("bad value on first cycle after reset deassertion");

  // Wrap from F to 0
  assert property (reset && $past(reset) && $past(count)==4'hF |-> count==4'h0)
    else $error("no wrap from 0xF to 0x0");

  // Coverage
  cover property ($fell(reset));
  cover property ($rose(reset));

  // Cover a full 16-step cycle after deassert (implies all states visited)
  cover property ($rose(reset)
                  ##1 (reset && $past(reset) && (count==$past(count)+4'd1))[*15]
                  ##1 (count==4'd0));

  // Hit representative states out of reset
  cover property (reset && count==4'd0);
  cover property (reset && count==4'd7);
  cover property (reset && count==4'd15);
endmodule

bind up_counter up_counter_sva sva_inst (.*);