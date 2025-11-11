// SVA for up_down_counter and shift_and_sum
// Bind these checkers to the DUTs

// Up/down counter checker
module up_down_counter_sva(input clk, input up_down, input [3:0] count);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Functional step (mod-16 wrap)
  property p_step_mod16;
    @(posedge clk) disable iff(!past_valid)
      count == ($past(count) + (up_down ? 4'd1 : 4'hF))[3:0];
  endproperty
  assert property (p_step_mod16);

  // Basic X-check after first cycle
  assert property (@(posedge clk) disable iff(!past_valid) !$isunknown(count));

  // Coverage: inc, dec, and both wrap-arounds
  cover property (@(posedge clk) past_valid && up_down);
  cover property (@(posedge clk) past_valid && !up_down);
  cover property (@(posedge clk) past_valid && $past(up_down)  && $past(count)==4'hF && count==4'h0);
  cover property (@(posedge clk) past_valid && !$past(up_down) && $past(count)==4'h0 && count==4'hF);
endmodule

bind up_down_counter up_down_counter_sva u_up_down_counter_sva(.clk(clk), .up_down(up_down), .count(count));


// Top-level checker focuses on connectivity, adder correctness, shift behavior, and counter coherence
module shift_and_sum_sva(
  input clk,
  input [3:0] A, B,
  input up_down,
  input [7:0] out,
  input [3:0] counter1_out, counter2_out, binary_adder_out
);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Adder correctness and out concatenation
  property p_adder_correct;
    @(posedge clk)
      binary_adder_out == (counter1_out + counter2_out)[3:0];
  endproperty
  assert property (p_adder_correct);

  assert property (@(posedge clk) out[3:0] == binary_adder_out);
  assert property (@(posedge clk) out[7:4] == (A >> B)[3:0]);

  // Two counters evolve with constant modular difference (same clk and control)
  property p_counters_delta_const;
    @(posedge clk) disable iff(!past_valid)
      (counter1_out - counter2_out)[3:0] == ($past(counter1_out) - $past(counter2_out))[3:0];
  endproperty
  assert property (p_counters_delta_const);

  // Basic X-checks on key combinational outputs
  assert property (@(posedge clk) !$isunknown({binary_adder_out, out}));

  // Coverage: up_down toggles, adder overflow, and shift edge cases
  cover property (@(posedge clk) past_valid && $rose(up_down));
  cover property (@(posedge clk) past_valid && $fell(up_down));
  cover property (@(posedge clk) (({1'b0,counter1_out}+{1'b0,counter2_out})[4] == 1'b1)); // carry-out
  cover property (@(posedge clk) B >= 4 && out[7:4] == 4'h0);
  cover property (@(posedge clk) B == 0 && out[7:4] == A);
endmodule

bind shift_and_sum shift_and_sum_sva u_shift_and_sum_sva(
  .clk(clk),
  .A(A),
  .B(B),
  .up_down(up_down),
  .out(out),
  .counter1_out(counter1_out),
  .counter2_out(counter2_out),
  .binary_adder_out(binary_adder_out)
);