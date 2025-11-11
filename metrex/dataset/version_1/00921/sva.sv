// SVA for module adder
module adder_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic [3:0]  sum,
  input  logic        carry
);

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always_ff @(posedge clk) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // Expected 5-bit result from previous cycle inputs
  let exp5 = $past({1'b0, A}) + $past({1'b0, B});

  // Reset behavior: clears outputs on next clock
  assert property (reset |=> {carry, sum} == 5'd0)
    else $error("Reset did not clear outputs");

  // Functional correctness: registered sum/carry equal prior-cycle A+B
  assert property (past_valid && !$past(reset) && !reset |-> {carry, sum} == exp5)
    else $error("Adder output mismatch: expected {%0b,%0h} got {%0b,%0h}", exp5[4], exp5[3:0], carry, sum);

  // No X/Z on outputs when inputs are known and not in/just after reset
  assert property (past_valid && !$past(reset) && !reset && !$isunknown({A,B}) |-> !$isunknown({sum,carry}))
    else $error("Unknown (X/Z) detected on outputs");

  // Coverage: reset pulses
  cover property ($rose(reset));
  cover property ($fell(reset));

  // Coverage: carry=0 and carry=1 cases (based on prior-cycle inputs)
  cover property (past_valid && !$past(reset) && exp5[4] == 1'b0);
  cover property (past_valid && !$past(reset) && exp5[4] == 1'b1);

  // Coverage: key corner cases
  cover property (past_valid && !$past(reset) && $past(A)==4'h0 && $past(B)==4'h0 |=> {carry,sum}==5'd0);
  cover property (past_valid && !$past(reset) && $past(A)==4'h8 && $past(B)==4'h8 |=> {carry,sum}==5'h10);
  cover property (past_valid && !$past(reset) && $past(A)==4'hF && $past(B)==4'hF |=> {carry,sum}==5'h1E);

endmodule

// Bind into DUT
bind adder adder_sva sva (
  .clk   (clk),
  .reset (reset),
  .A     (A),
  .B     (B),
  .sum   (sum),
  .carry (carry)
);