// SVA for top_module and its sub-blocks
// Bind this file to the DUT:  bind top_module top_module_sva u_sva(.*);

module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        shift_left,
  input  logic        shift_right,
  input  logic [3:0]  q,
  input  logic [3:0]  counter_out,
  input  logic [3:0]  shift_register_out,
  input  logic [3:0]  functional_out
);

  // Helpers
  function automatic [3:0] add4(input [3:0] a, b);
    add4 = a + b; // 4-bit truncation (mod-16)
  endfunction

  function automatic [3:0] func_exp(input [3:0] cnt, sreg);
    func_exp = add4(cnt, sreg) ^ 4'hA;
  endfunction

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Reset behavior (asynchronous reset checked at clock edge)
  assert property (@(posedge clk) reset |-> (counter_out == 4'h0))
    else $error("Counter not zero during reset");

  assert property (@(posedge clk) reset |-> (shift_register_out == 4'h0))
    else $error("Shift register not zero during reset");

  // Counter increments mod-16
  assert property (@(posedge clk) disable iff (reset)
                   past_valid |-> (($past(counter_out) == 4'hF) ?
                                    (counter_out == 4'h0) :
                                    (counter_out == ($past(counter_out) + 4'h1))))
    else $error("Counter failed to increment mod-16");

  // Shift-register hold when idle
  assert property (@(posedge clk) disable iff (reset)
                   past_valid && !$past(shift_left) && !$past(shift_right)
                   |-> (shift_register_out == $past(shift_register_out)))
    else $error("Shift register failed to hold value when idle");

  // Shift left (wins over right if both asserted)
  assert property (@(posedge clk) disable iff (reset)
                   past_valid && $past(shift_left)
                   |-> (shift_register_out ==
                        { $past(shift_register_out[2:0]), $past(counter_out[3]) }))
    else $error("Shift-left behavior incorrect (including precedence)");

  // Shift right (only when left is not asserted)
  assert property (@(posedge clk) disable iff (reset)
                   past_valid && !$past(shift_left) && $past(shift_right)
                   |-> (shift_register_out ==
                        { $past(counter_out[0]), $past(shift_register_out[3:1]) }))
    else $error("Shift-right behavior incorrect");

  // Functional correctness
  assert property (@(posedge clk) (functional_out == func_exp(counter_out, shift_register_out)))
    else $error("functional_out mismatch");

  assert property (@(posedge clk) (q == functional_out))
    else $error("q != functional_out");

  // Optional X/Z checks after first cycle out of reset
  assert property (@(posedge clk) past_valid && !reset |-> !$isunknown({q, counter_out, shift_register_out, functional_out}))
    else $error("X/Z detected on key signals");

  // Coverage
  cover property (@(posedge clk) reset ##1 !reset);                              // reset deasserts
  cover property (@(posedge clk) disable iff (reset) past_valid &&
                  $past(counter_out)==4'hF ##1 counter_out==4'h0);               // counter wrap
  cover property (@(posedge clk) disable iff (reset) past_valid && $past(shift_left));       // left shift seen
  cover property (@(posedge clk) disable iff (reset) past_valid && $past(shift_right) && !$past(shift_left)); // right shift seen
  cover property (@(posedge clk) disable iff (reset) past_valid && $past(shift_left) && $past(shift_right));  // both asserted (precedence)

endmodule

bind top_module top_module_sva u_sva (
  .clk(clk),
  .reset(reset),
  .shift_left(shift_left),
  .shift_right(shift_right),
  .q(q),
  .counter_out(counter_out),
  .shift_register_out(shift_register_out),
  .functional_out(functional_out)
);