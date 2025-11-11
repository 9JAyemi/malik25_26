// SVA for shift_register: concise, high-quality checks and coverage
module shift_register_sva #(parameter int DATA_WIDTH = 8) (
  input  logic                       clk,
  input  logic                       reset,
  input  logic                       shift_in,
  input  logic                       shift_out,
  input  logic [DATA_WIDTH-1:0]      buffer
);

  default clocking cb @(posedge clk); endclocking

  // Synchronous reset: zeroization next cycle
  assert property (@cb reset |=> (buffer == '0 && shift_out == 1'b0))
    else $error("Reset did not zeroize buffer/shift_out on next cycle");

  // While/after reset held, state must be zeros
  assert property (@cb $past(reset) |-> (buffer == '0 && shift_out == 1'b0))
    else $error("State not zero while/after reset");

  // Bit-accurate shift behavior (guard out cycles adjacent to reset)
  // MSB receives shift_in
  assert property (@cb (!reset && !$past(reset)) |-> buffer[DATA_WIDTH-1] == $past(shift_in))
    else $error("MSB not loaded from shift_in");

  // Each bit shifts down by 1
  genvar i;
  generate
    for (i = 1; i < DATA_WIDTH; i++) begin : g_shift_down
      assert property (@cb (!reset && !$past(reset)) |-> buffer[i-1] == $past(buffer[i]))
        else $error("Buffer bit %0d did not shift from bit %0d", i-1, i);
    end
  endgenerate

  // Output is previous LSB
  assert property (@cb (!reset && !$past(reset)) |-> shift_out == $past(buffer[0]))
    else $error("shift_out not equal to previous LSB");

  // End-to-end latency: input bit emerges at shift_out after DATA_WIDTH+1 clocks (no reset in the window)
  assert property (@cb disable iff (reset)
                   shift_out == $past(shift_in, DATA_WIDTH+1, reset))
    else $error("End-to-end latency mismatch");

  // Coverage
  // 1) A '1' injected appears at shift_out after the expected latency
  cover property (@cb disable iff (reset) shift_in ##(DATA_WIDTH+1) shift_out);

  // 2) A '0' injected appears at shift_out after the expected latency
  cover property (@cb disable iff (reset) !shift_in ##(DATA_WIDTH+1) !shift_out);

  // 3) Reset deassert followed by quiet output window (pipeline flush from zeros)
  cover property (@cb $fell(reset) ##[1:DATA_WIDTH+1] (shift_out == 1'b0));

endmodule

// Bind into DUT (assumes internal signal name 'buffer' is accessible)
bind shift_register shift_register_sva #(.DATA_WIDTH(DATA_WIDTH)) shift_register_sva_i (
  .clk      (clk),
  .reset    (reset),
  .shift_in (shift_in),
  .shift_out(shift_out),
  .buffer   (buffer)
);