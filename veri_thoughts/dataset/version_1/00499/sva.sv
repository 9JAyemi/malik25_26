// SVA for shift_register
module shift_register_sva #(parameter WIDTH=4)
(
  input clk, reset, parallel_load, shift_left, shift_right,
  input [WIDTH-1:0] parallel_input,
  input [WIDTH-1:0] q
);

  default clocking @(posedge clk); endclocking

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Functional correctness and priority
  assert property (reset |=> q == '0);

  assert property (disable iff(!past_valid)
    (!reset && parallel_load) |=> q == $past(parallel_input));

  assert property (disable iff(!past_valid)
    (!reset && !parallel_load && shift_left) |=> q == {$past(q[WIDTH-2:0]), 1'b0});

  assert property (disable iff(!past_valid)
    (!reset && !parallel_load && !shift_left && shift_right) |=> q == {1'b0, $past(q[WIDTH-1:1])});

  assert property (disable iff(!past_valid)
    (!reset && !parallel_load && !shift_left && !shift_right) |=> q == $past(q));

  // Explicit left-over-right priority when both asserted
  assert property (disable iff(!past_valid)
    (!reset && !parallel_load && shift_left && shift_right)
      |=> q == {$past(q[WIDTH-2:0]), 1'b0});

  // Coverage
  cover property (reset);
  cover property (!reset && parallel_load);
  cover property (!reset && !parallel_load && shift_left);
  cover property (!reset && !parallel_load && !shift_left && shift_right);
  cover property (!reset && !parallel_load && !shift_left && !shift_right);
  cover property (!reset && !parallel_load && shift_left && shift_right); // priority exercised
  cover property (reset && parallel_load); // reset overrides load
  cover property ( (!reset && parallel_load)
                   ##1 (!reset && !parallel_load && shift_left)
                   ##1 (!reset && !parallel_load && !shift_left && shift_right) );

endmodule

// Bind into DUT
bind shift_register shift_register_sva #(.WIDTH(4)) sva_i (
  .clk, .reset, .parallel_load, .shift_left, .shift_right, .parallel_input, .q
);