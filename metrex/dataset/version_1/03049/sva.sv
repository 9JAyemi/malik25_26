// SVA checker for adder. Bind to DUT to access internal carry.
module adder_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        enable,
  input  logic [3:0]  a,
  input  logic [3:0]  b,
  input  logic [3:0]  sum,
  input  logic [3:0]  carry
);
  default clocking cb @(posedge clk); endclocking

  // Safe $past usage
  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic sanity: no X/Z on key signals once we have history
  assert property (past_valid |-> !$isunknown({reset,enable,a,b,sum,carry}));

  // Reset clears outputs (observed one cycle after reset asserted)
  assert property (past_valid && $past(reset) |-> (sum==4'h0 && carry==4'h0));

  // When disabled (and not in reset), outputs clear on next cycle
  assert property (past_valid && $past(!reset && !enable) |-> (sum==4'h0 && carry==4'h0));

  // When enabled (and not in reset), outputs update per RTL arithmetic width rules
  // Note: a,b,carry are 4-bit; a+b+carry is 4-bit; {carry,sum} must equal zero-extended 4-bit result
  assert property (past_valid && $past(!reset && enable)
                   |-> {carry,sum} == ($past(a) + $past(b) + $past(carry)));

  // Outputs must remain known during reset as well
  assert property (reset |-> !$isunknown({sum,carry}));

  // Coverage: exercise reset, enable, overflow vs. no-overflow cases
  cover property (past_valid && $past(reset) && !reset); // reset deassert
  cover property (past_valid && $past(!reset && enable)); // enabled path taken
  cover property (past_valid && $past(!reset && !enable)); // disabled path taken
  cover property (past_valid && $past(!reset && enable)
                  && (($past(a)+$past(b)+$past(carry)) <= 4'hF)); // no overflow
  cover property (past_valid && $past(!reset && enable)
                  && (($past(a)+$past(b)+$past(carry)) > 4'hF)); // overflow stimulus
  // This cover will not hit with current RTL (carry remains zero due to 4-bit sum truncation)
  cover property (carry != 4'h0);

endmodule

// Bind into the DUT to observe internal 'carry'
bind adder adder_sva u_adder_sva (.* , .carry(carry));