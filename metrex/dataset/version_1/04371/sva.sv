// SVA for async_reset_release
module async_reset_release_sva (
  input logic        clk,
  input logic        reset,
  input logic        rst,
  input logic [3:0]  counter,
  input logic        rst_active
);
  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on key signals
  assert property (!$isunknown({reset,rst,counter})));

  // While reset is low, hold in reset state
  assert property (!reset |-> (counter==4'd0 && rst==1'b1));

  // On reset release edge (first clk after), still in reset state
  assert property ($rose(reset) |-> (counter==4'd0 && rst==1'b1));

  // While reset is high and counter < 10: count up by 1 next cycle; rst stays asserted
  assert property (reset && counter < 4'd10 |=> (counter == $past(counter)+4'd1) && rst==1'b1);

  // Counter never exceeds 10 when reset is high
  assert property (reset |-> (counter <= 4'd10));

  // When counter is 10, next cycle rst deasserts and counter holds at 10
  assert property (reset && counter==4'd10 |=> (rst==1'b0 && counter==4'd10));

  // After rst deasserts (with reset high), it stays deasserted and counter stays at 10
  assert property (reset && $past(reset) && $past(rst)==1'b0 |-> (rst==1'b0 && counter==4'd10));

  // No synchronous rise of rst while reset is stably high
  assert property (reset && $past(reset) |-> !$rose(rst));

  // Output must mirror internal flop
  assert property (rst == rst_active);

  // Coverage: see a full release to rst deassert within 12 clocks
  cover property ($rose(reset) ##[1:12] $fell(rst));

  // Coverage: hit counter==10 with reset high
  cover property (reset ##[1:$] counter==4'd10 ##1 rst==1'b0);
endmodule

bind async_reset_release async_reset_release_sva
  (.clk(clk), .reset(reset), .rst(rst), .counter(counter), .rst_active(rst_active));