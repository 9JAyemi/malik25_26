// SVA for counter: concise checks + coverage
module counter_sva (
  input clk,
  input rst,
  input [1:0] count
);

  default clocking @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;

  default disable iff (!past_valid);

  // Reset behavior
  assert property (rst |=> count == 2'b00);                  // next cycle after rst: count=0
  assert property ($past(rst) && rst |-> count == 2'b00);    // held reset keeps count at 0

  // Next-state function when not in reset
  assert property (!rst |=> count == (($past(count)==2'b11) ? 2'b00 : $past(count)+2'b01));

  // First cycle after reset deasserts increments from 0 to 1
  assert property ($past(rst) && !rst |=> count == 2'b01);

  // No glitches between clock edges (synchronous update only)
  assert property (@(negedge clk) $stable(count));

  // Coverage
  cover property (!rst && count==2'b11 |=> count==2'b00);    // wrap 3->0
  cover property (!rst && count==2'b00 ##1 !rst && count==2'b01
                  ##1 !rst && count==2'b10 ##1 !rst && count==2'b11
                  ##1 !rst && count==2'b00);                 // full cycle 0->1->2->3->0
  cover property ($rose(rst) ##[1:$] $fell(rst));            // a reset pulse occurs

endmodule

bind counter counter_sva sva_counter_i (.clk(clk), .rst(rst), .count(count));