// SVA for RCB_FRL_COUNT_TO_64
// Bind this module to the DUT for checks and coverage.

module RCB_FRL_COUNT_TO_64_sva (
  input logic        clk,
  input logic        rst,
  input logic        count,
  input logic        ud,
  input logic [5:0]  counter_value
);

  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on interface
  assert property (@cb !$isunknown({rst,count,ud}));
  assert property (@cb !$isunknown(counter_value));

  // Async reset behavior
  assert property (@(posedge rst) counter_value == 6'h00);
  assert property (@cb rst |-> counter_value == 6'h00);

  // Functional behavior (mod-64), disabled during reset
  // Hold when count==0 (regardless of ud)
  assert property (@cb disable iff (rst)
                   !count |-> $stable(counter_value));

  // Increment when count==1 && ud==1
  assert property (@cb disable iff (rst)
                   (count && ud) |=> counter_value == $past(counter_value) + 6'd1);

  // Decrement when count==1 && ud==0
  assert property (@cb disable iff (rst)
                   (count && !ud) |=> counter_value == $past(counter_value) - 6'd1);

  // Explicit wrap checks
  assert property (@cb disable iff (rst)
                   ($past(counter_value)==6'h3F && count && ud) |=> counter_value == 6'h00);
  assert property (@cb disable iff (rst)
                   ($past(counter_value)==6'h00 && count && !ud) |=> counter_value == 6'h3F);

  // Coverage: exercise all behaviors
  cover property (@cb disable iff (rst)
                  (count && ud) ##1 counter_value == $past(counter_value)+6'd1); // up
  cover property (@cb disable iff (rst)
                  (count && !ud) ##1 counter_value == $past(counter_value)-6'd1); // down
  cover property (@cb disable iff (rst)
                  ({count,ud}==2'b00) ##1 $stable(counter_value)); // hold (00)
  cover property (@cb disable iff (rst)
                  ({count,ud}==2'b01) ##1 $stable(counter_value)); // hold (01)
  cover property (@cb disable iff (rst)
                  ($past(counter_value)==6'h3F && $past(count && ud)) ##1 counter_value==6'h00); // up wrap
  cover property (@cb disable iff (rst)
                  ($past(counter_value)==6'h00 && $past(count && !ud)) ##1 counter_value==6'h3F); // down wrap

endmodule

bind RCB_FRL_COUNT_TO_64 RCB_FRL_COUNT_TO_64_sva
(
  .clk(clk),
  .rst(rst),
  .count(count),
  .ud(ud),
  .counter_value(counter_value)
);