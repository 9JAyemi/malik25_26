// SVA for binary_counter
module binary_counter_sva (
  input logic       clk,
  input logic       reset,
  input logic [3:0] count
);

  // Default sampling on clk
  default clocking cb @(posedge clk); endclocking

  // Async reset drives 0 immediately and is known
  assert property (@(posedge reset) count == 4'd0 && !$isunknown(count))
    else $error("Async reset did not force count=0 or count unknown");

  // While reset is high at a clk edge, count must be 0
  assert property (@(posedge clk) reset |-> count == 4'd0)
    else $error("Count not 0 during reset at clk edge");

  // Count must be known at clk edges
  assert property (@(posedge clk) !$isunknown(count))
    else $error("Count has X/Z at clk edge");

  // Count stays within 0..9 when not in reset
  assert property (@(posedge clk) disable iff (reset)
                   count <= 4'd9)
    else $error("Count out of range (>9)");

  // Normal step behavior: +1 each cycle, wrap 9->0 (skip first cycle after reset)
  assert property (@(posedge clk) disable iff (reset)
                   $past(!reset) |-> count == (($past(count) == 4'd9) ? 4'd0 : $past(count) + 4'd1))
    else $error("Illegal transition (not +1 or 9->0)");

  // First active cycle after reset: 0 -> 1
  assert property (@(posedge clk)
                   $past(reset) && !reset |-> count == $past(count) + 4'd1)
    else $error("Did not increment from 0 after reset deassert");

  // Coverage
  // See a full 0..9..0 cycle (with reset low throughout)
  cover property (@(posedge clk) disable iff (reset)
                  (count==4'd0) ##1 (count==4'd1) ##1 (count==4'd2) ##1 (count==4'd3) ##1
                  (count==4'd4) ##1 (count==4'd5) ##1 (count==4'd6) ##1 (count==4'd7) ##1
                  (count==4'd8) ##1 (count==4'd9) ##1 (count==4'd0));

  // See a wrap event 9->0
  cover property (@(posedge clk) disable iff (reset)
                  $past(!reset) && $past(count)==4'd9 && count==4'd0);

  // See an asynchronous reset event
  cover property (@(posedge reset) 1'b1);

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva u_binary_counter_sva(.clk(clk), .reset(reset), .count(count));