// SVA for clock_divider
// Focused, concise checks + coverage. Bind to DUT to access internal counter.

module clock_divider_sva #(parameter int unsigned DIVISOR = 2)
(
  input  logic        clock,
  input  logic        reset,
  input  logic        clk_out,
  input  logic [31:0] counter
);
  // Sanity
  initial if (DIVISOR == 0) $fatal(1, "DIVISOR must be > 0");

  // Make $past safe and handle async reset
  logic past_valid;
  always @(posedge clock or posedge reset)
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;

  default clocking cb @(posedge clock); endclocking
  default disable iff (reset || !past_valid);

  // Reset state at sampling edge
  assert property (@cb reset |-> (clk_out == 1'b0 && counter == 32'd0));

  // Invariant: counter stays in range [0 .. DIVISOR-1]
  assert property (@cb counter < DIVISOR);

  // Step-wise transition: increment when not at terminal count; clk_out stable
  assert property (@cb ($past(counter) < DIVISOR-1)
                       |-> (counter == $past(counter) + 1) && $stable(clk_out));

  // Step-wise transition: wrap when at terminal count; clk_out toggles
  assert property (@cb ($past(counter) == DIVISOR-1)
                       |-> (counter == 32'd0) && $changed(clk_out));

  // Periodicity: exactly DIVISOR cycles between consecutive clk_out edges
  assert property (@cb $changed(clk_out)
                       |=> (!$changed(clk_out))[* (DIVISOR-1)] ##1 $changed(clk_out));

  // No spurious toggles when counter not at terminal count
  assert property (@cb (counter != DIVISOR-1) |-> $stable(clk_out));

  // Coverage
  cover property (@cb $fell(reset) ##1 !$changed(clk_out)[* (DIVISOR-1)] ##1 $changed(clk_out)); // first toggle after reset
  cover property (@cb $changed(clk_out) ##1 !$changed(clk_out)[* (DIVISOR-1)] ##1 $changed(clk_out)); // one half-period
  cover property (@cb ($past(counter) < DIVISOR-1) ##1 (counter == $past(counter) + 1)); // increment branch
  cover property (@cb ($past(counter) == DIVISOR-1) ##1 (counter == 32'd0) && $changed(clk_out)); // wrap branch
endmodule

// Bind into DUT
bind clock_divider clock_divider_sva #(.DIVISOR(divisor))
  clock_divider_sva_i (.clock(clock), .reset(reset), .clk_out(clk_out), .counter(counter));