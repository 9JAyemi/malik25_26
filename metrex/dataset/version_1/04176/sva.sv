// SVA for counter
module counter_sva (
  input logic        clk,
  input logic        rst,
  input logic [31:0] max_value,
  input logic [31:0] count
);

  // No X/Z on key signals at clk edge
  assert property (@(posedge clk) !$isunknown({rst, max_value, count})) else $error("X/Z on rst/max_value/count");

  // Asynchronous reset drives zero immediately and holds while asserted
  assert property (@(posedge rst) ##0 (count == 32'd0)) else $error("count not zero on async rst");
  assert property (@(posedge clk) rst |-> (count == 32'd0)) else $error("count not zero while rst=1");

  // Next-state functional checks (use current max_value, previous count)
  // Wrap case
  assert property (@(posedge clk)
    (!rst && !$isunknown($past(count)) && !$isunknown(max_value) &&
     ($past(count) == (max_value - 32'd1)))
    |-> (count == 32'd0)
  ) else $error("Wrap behavior incorrect");

  // Increment case
  assert property (@(posedge clk)
    (!rst && !$isunknown($past(count)) && !$isunknown(max_value) &&
     ($past(count) != (max_value - 32'd1)))
    |-> (count == ($past(count) + 32'd1))
  ) else $error("Increment behavior incorrect");

  // Coverage
  cover property (@(posedge rst) ##0 (count == 32'd0)); // async reset observed
  cover property (@(posedge clk)
    (!rst && !$isunknown($past(count)) && !$isunknown(max_value) &&
     ($past(count) != (max_value - 32'd1)) && (count == $past(count) + 32'd1))
  ); // increment step
  cover property (@(posedge clk)
    (!rst && !$isunknown($past(count)) && !$isunknown(max_value) &&
     ($past(count) == (max_value - 32'd1)) ##1 (!rst && (count == 32'd0)))
  ); // wrap step
  cover property (@(posedge clk) !rst && (max_value == 32'd1) ##1 (!rst && (count == 32'd0))); // max=1 wrap case

endmodule

bind counter counter_sva u_counter_sva (.*);