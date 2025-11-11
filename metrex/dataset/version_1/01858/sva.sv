// SVA for counter
module counter_sva (
  input logic        clk,
  input logic        rst,
  input logic [31:0] max_val,
  input logic [31:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (rst |=> count == 32'd0);
  assert property ($past(rst) && rst |-> count == 32'd0);

  // State update when not in reset: next = (count==max_val) ? 0 : count+1
  assert property (!rst |=> count == (($past(count) == $past(max_val)) ? 32'd0 : ($past(count) + 32'd1)));

  // Key functional covers
  cover property (!rst && (count != max_val) ##1 count == ($past(count) + 32'd1)); // increment
  cover property (!rst && (count == max_val) ##1 count == 32'd0);                  // wrap
  cover property (rst ##1 rst ##1 !rst);                                          // held reset then release

endmodule

bind counter counter_sva counter_sva_i (.*);