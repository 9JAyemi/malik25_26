// SVA for binary_counter
module binary_counter_sva (
  input clk,
  input rst,
  input en,
  input ld,
  input [3:0] load_data,
  input [3:0] count
);

  // Make $past safe
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Basic sanity
  assert property (!$isunknown(count)));

  // Synchronous reset
  assert property (rst |=> count == 4'd0);

  // Hold when not enabled (ld irrelevant)
  assert property (!rst && !en |=> count == $past(count));

  // Load when enabled and ld asserted
  assert property (!rst && en && ld |=> count == $past(load_data));

  // Increment by 1 mod 16 when enabled and ld deasserted
  assert property (!rst && en && !ld |=> count == (($past(count) + 4'd1) & 4'hF));

  // Coverage
  cover property (rst |=> count == 4'd0);
  cover property (!rst && en && ld |=> count == $past(load_data));
  cover property (!rst && en && !ld |=> count == (($past(count) + 4'd1) & 4'hF));
  cover property (!rst && en && !ld && ($past(count) == 4'hF) |=> count == 4'h0);

endmodule

bind binary_counter binary_counter_sva sva_inst (
  .clk(clk),
  .rst(rst),
  .en(en),
  .ld(ld),
  .load_data(load_data),
  .count(count)
);