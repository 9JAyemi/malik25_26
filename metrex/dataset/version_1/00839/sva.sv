// SVA for top_module
// Bind-in checker focusing on counter behavior, async reset, and adder logic

module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        up_down,
  input  logic [1:0]  input_value,
  input  logic [1:0]  output_value,
  input  logic [2:0]  counter_output,
  // internal DUT signals (bound hierarchically)
  input  logic [2:0]  counter,
  input  logic [1:0]  sum,
  input  logic        carry_out
);
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset behavior
  // Immediate effect at reset assertion (allow NBA update via ##0)
  assert property (@(posedge reset) ##0 (counter == 3'd0));
  // Held reset forces counter/counter_output to 0 on every clk edge
  assert property (@(posedge clk) reset |-> (counter == 3'd0 && counter_output == 3'd0));

  // counter_output must mirror internal counter
  assert property (@(posedge clk) counter_output == counter);

  // Up/down 3-bit modulo-8 step (wraps naturally)
  assert property (@(posedge clk) disable iff (reset)
                   counter_output == $past(counter_output) + (up_down ? 3'd1 : 3'd7));

  // Combinational adder correctness (from spec)
  assert property (@(posedge clk)
                   output_value[0] == (counter_output[0] ^ input_value[0]));
  assert property (@(posedge clk)
                   output_value[1] == ((counter_output[1] ^ input_value[1]) ^
                                       (counter_output[0] & input_value[0])));

  // Internal net consistency
  assert property (@(posedge clk) output_value == sum);
  assert property (@(posedge clk)
                   carry_out == ((counter[1] & input_value[1]) |
                                 (counter[0] & input_value[0])));

  // No X/Z on observable outputs after reset released
  assert property (@(posedge clk) disable iff (reset)
                   !$isunknown({counter_output, output_value}));

  // Focused functional coverage
  // Wrap-around in both directions
  cover property (@(posedge clk) disable iff (reset)
                  $past(counter_output) == 3'd7 && up_down && counter_output == 3'd0);
  cover property (@(posedge clk) disable iff (reset)
                  $past(counter_output) == 3'd0 && !up_down && counter_output == 3'd7);

  // Sustained counting in both modes
  cover property (@(posedge clk) disable iff (reset) up_down ##1 up_down ##1 up_down);
  cover property (@(posedge clk) disable iff (reset) !up_down ##1 !up_down ##1 !up_down);

  // Exercise all input_value combinations
  cover property (@(posedge clk) disable iff (reset) input_value == 2'b00);
  cover property (@(posedge clk) disable iff (reset) input_value == 2'b01);
  cover property (@(posedge clk) disable iff (reset) input_value == 2'b10);
  cover property (@(posedge clk) disable iff (reset) input_value == 2'b11);

  // Adder carry generation cases
  cover property (@(posedge clk) disable iff (reset) (counter_output[0] & input_value[0])); // LSB carry
  cover property (@(posedge clk) disable iff (reset) carry_out); // final carry_out high
endmodule

bind top_module top_module_sva sva_i (
  .clk(clk),
  .reset(reset),
  .up_down(up_down),
  .input_value(input_value),
  .output_value(output_value),
  .counter_output(counter_output),
  .counter(counter),
  .sum(sum),
  .carry_out(carry_out)
);