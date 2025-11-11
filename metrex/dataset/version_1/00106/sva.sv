// SVA for counter. Bind this to the DUT.

module counter_sva (input logic clk, input logic rst, input logic [3:0] count);

  default clocking cb @(posedge clk); endclocking

  // No X/Z on key signals at clock edges
  assert property (!$isunknown({rst, count})))
    else $error("X/Z detected on rst or count");

  // Count is always within 0..9
  assert property (count <= 4'd9)
    else $error("Count out of range > 9");

  // While in reset, count must be 0 (synchronous check)
  assert property (!rst |-> (count == 4'd0))
    else $error("Count not 0 during reset");

  // Asynchronous reset immediately clears count to 0
  assert property (@(negedge rst) ##0 (count == 4'd0))
    else $error("Async reset did not clear count to 0");

  // Normal increment when not wrapping
  assert property (rst && $past(rst) && ($past(count) != 4'd9) |-> (count == $past(count)+1))
    else $error("Count failed to increment by 1");

  // Wrap from 9 to 0
  assert property (rst && $past(rst) && ($past(count) == 4'd9) |-> (count == 4'd0))
    else $error("Count failed to wrap 9->0");

  // Deasserting reset leads to 1 on the next clock (since reset drives 0)
  assert property ($rose(rst) |-> (count == 4'd1))
    else $error("Post-reset first count not 1");

  // Zero can only occur after wrap (not counting reset cycles)
  assert property (rst && $past(rst) && (count == 4'd0) |-> ($past(count) == 4'd9))
    else $error("Count reached 0 without prior 9 (outside reset)");

  // Coverage

  // Observe full 0..9..0 cycle without reset
  cover property (disable iff (!rst)
                  (count==4'd0) ##1 (count==4'd1) ##1 (count==4'd2) ##1 (count==4'd3) ##1
                  (count==4'd4) ##1 (count==4'd5) ##1 (count==4'd6) ##1 (count==4'd7) ##1
                  (count==4'd8) ##1 (count==4'd9) ##1 (count==4'd0));

  // Observe wrap 8->9->0
  cover property (disable iff (!rst) (count==4'd8) ##1 (count==4'd9) ##1 (count==4'd0));

  // Observe asynchronous reset event
  cover property (@(negedge rst) 1'b1);

  // Observe reset deassert followed by count=1
  cover property ($rose(rst) ##1 (count==4'd1));

endmodule

bind counter counter_sva i_counter_sva (.clk(clk), .rst(rst), .count(count));