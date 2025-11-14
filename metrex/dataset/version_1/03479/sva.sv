// SVA for my_module
module my_module_sva (
  input clk,
  input rst,
  input [15:0] data_in,
  input [15:0] data_out,
  input        valid,
  input [15:0] prev_data_in
);

  logic past_valid; initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Reset behavior (same cycle)
  assert property (rst |-> (data_out == 16'h0000 && valid == 1'b0 && prev_data_in === data_in));

  // Update on input change
  assert property (disable iff (!past_valid || rst)
                   (data_in !== $past(prev_data_in)) |-> (data_out === ~data_in && valid == 1'b1 && prev_data_in === data_in));

  // Hold when no change
  assert property (disable iff (!past_valid || rst)
                   (data_in === $past(prev_data_in)) |-> (data_out === $past(data_out) && valid === $past(valid) && prev_data_in === $past(prev_data_in)));

  // No spurious changes
  assert property (disable iff (!past_valid || rst)
                   $changed(data_out) |-> (data_in !== $past(prev_data_in)));
  assert property (disable iff (!past_valid || rst)
                   $changed(valid)    |-> (data_in !== $past(prev_data_in)));
  assert property (disable iff (!past_valid || rst)
                   $changed(prev_data_in) |-> (data_in !== $past(prev_data_in)));

  // Valid can only fall when rst asserted
  assert property (disable iff (!past_valid) $fell(valid) |-> rst);

  // Coverage
  cover property (rst);
  cover property (disable iff (!past_valid || rst) (data_in !== $past(prev_data_in)));
  cover property (disable iff (!past_valid || rst) (data_in === $past(prev_data_in)));
  cover property (disable iff (!past_valid || rst)
                  (data_in !== $past(prev_data_in)) ##1 (data_in === $past(prev_data_in)) ##1 (data_in !== $past(prev_data_in)));

endmodule

// Bind into DUT (accesses internal prev_data_in)
bind my_module my_module_sva sva_inst(.clk(clk), .rst(rst), .data_in(data_in), .data_out(data_out), .valid(valid), .prev_data_in(prev_data_in));