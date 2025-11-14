// SVA for priority_encoder
module priority_encoder_sva (input logic clk, input logic [1:0] data, input logic q);

  default clocking cb @(posedge clk); endclocking

  bit f_past_valid;
  initial f_past_valid = 1'b0;
  always @(posedge clk) f_past_valid <= 1'b1;

  // q is the registered version of data[1]
  assert property (disable iff (!f_past_valid)
                   !$isunknown($past(data[1])) |-> (q == $past(data[1]) && !$isunknown(q)));

  // X-propagation: unknown data[1] yields unknown q
  assert property (disable iff (!f_past_valid)
                   $isunknown($past(data[1])) |-> $isunknown(q));

  // q only changes on the rising edge of clk (no glitches)
  assert property (@(posedge q or negedge q) $rose(clk));

  // Coverage
  cover property (q == 0);
  cover property (q == 1);
  cover property ($rose(data[1]));     // observe 0->1 on data[1]
  cover property ($fell(data[1]));     // observe 1->0 on data[1]
  cover property (disable iff (!f_past_valid) $rose(data[1]) ##1 (q == 1));
  cover property (disable iff (!f_past_valid) $fell(data[1]) ##1 (q == 0));

endmodule

bind priority_encoder priority_encoder_sva sva_i (.clk(clk), .data(data), .q(q));