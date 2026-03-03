// SVA for binary_counter
module binary_counter_sva #(parameter N=4)(
  input  logic              clk,
  input  logic              reset,
  input  logic [N-1:0]      count
);

  // establish a safe $past window
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // default clock
  default clocking cb @(posedge clk); endclocking

  // 1) Synchronous reset clears count on the next clock
  assert property (reset |=> count == '0);

  // 2) When previous cycle was not reset, counter increments by 1 (mod 2^N)
  assert property (past_valid && !$past(reset) |-> count == $past(count) + 1);

  // 3) Explicitly check wrap from max -> 0 on increment
  assert property (past_valid && !$past(reset) && ($past(count) == {N{1'b1}}) |-> count == '0);

  // 4) No unknowns on count once we have at least one sample
  assert property (past_valid |-> !$isunknown(count));

  // Coverage
  cover property (reset);                               // saw reset asserted
  cover property ($rose(reset));                        // reset rise
  cover property ($fell(reset));                        // reset deassert
  cover property (past_valid && !$past(reset) &&       // observed a wrap event
                  ($past(count) == {N{1'b1}}) && (count == '0));
  // From a reset, observe first increment 0 -> 1
  cover property ($past(reset) && !reset && (count == $past(count) + 1));

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva #(.N(N))
  binary_counter_sva_i (.clk(clk), .reset(reset), .count(count));