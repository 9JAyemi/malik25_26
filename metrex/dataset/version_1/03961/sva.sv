// SVA for signed_non_restoring_divider
// Bind-friendly, concise, high-signal-coverage

checker snrdiv_sva (
  input  logic                     clk,
  input  logic signed [31:0]       dividend,
  input  logic signed [31:0]       divisor,
  input  logic signed [31:0]       quotient,
  input  logic signed [31:0]       remainder,
  input  logic signed [31:0]       dividend_reg,
  input  logic signed [31:0]       divisor_reg,
  input  logic signed [31:0]       quotient_reg,
  input  logic signed [31:0]       adder_input,
  input  logic signed [31:0]       adder_output,
  input  logic       [4:0]         count,
  input  logic                     sign
);
  default clocking cb @(posedge clk); endclocking

  let sabs32(v) = v[31] ? -v : v;

  // Environment assumptions (keep DUT well-defined)
  assume property (count == 0 |-> divisor != 0);
  assume property ($rose(count == 0) |-> ($stable(dividend) && $stable(divisor)) [*17]);

  // Sanity: no X on key inputs at start of an operation
  assert property ($rose(count == 0) |-> !$isunknown({dividend, divisor}));

  // Count must increment by 1 modulo 32
  assert property (!$isunknown($past(count)) |-> count == $past(count) + 5'd1);

  // Initialization on start
  assert property ($past(count) == 0 |-> (remainder == dividend_reg && quotient_reg == 0));

  // Sign computation is consistent with operand signs
  assert property (sign == (dividend[31] ^ divisor[31]));

  // Branch decisions set quotient bit correctly
  assert property ($past(count) > 0 && $past(remainder) < 0  |-> quotient_reg[$past(count)-1] == 1'b0);
  assert property ($past(count) > 0 && $past(remainder) >= 0 |-> quotient_reg[$past(count)-1] == 1'b1);

  // Adder datapath consistency per branch
  assert property ($past(count) > 0 && $past(remainder) < 0  |->
                   adder_input  == (divisor_reg - $past(remainder)) &&
                   adder_output == ($past(remainder) + adder_input) &&
                   remainder    == adder_output);

  assert property ($past(count) > 0 && $past(remainder) >= 0 |->
                   adder_input  == ($past(remainder) - divisor_reg) &&
                   adder_output == ($past(remainder) - adder_input) &&
                   remainder    == adder_output);

  // Non-restoring invariant: remainder is bounded by +/-|divisor| (when divisor != 0)
  assert property ($past(count) > 0 && divisor != 0 |->
                   (-sabs32(divisor_reg) <= remainder) && (remainder <= sabs32(divisor_reg)));

  // Completion transfer: quotient mirrors internal register at count==16
  assert property ($past(count) == 16 |-> quotient == $past(quotient_reg));

  // Final sign of quotient should match expected sign
  assert property ($past(count) == 16 |-> quotient[31] == sign);

  // Functional correctness at completion (under stability + nonzero divisor)
  assert property ($past(count) == 16 && divisor != 0 |->
                   quotient == ($signed(dividend) / $signed(divisor)));

  // No X on output at completion
  assert property ($past(count) == 16 |-> !$isunknown(quotient));

  // Coverage: reach a full 16-cycle operation from start
  cover property (count == 0 ##16 (count == 16));

  // Coverage: both branch directions exercised
  cover property ($past(count) > 0 && $past(remainder) < 0);
  cover property ($past(count) > 0 && $past(remainder) >= 0);

  // Coverage: both overall signs observed at start
  cover property ($rose(count == 0) && sign == 1'b0);
  cover property ($rose(count == 0) && sign == 1'b1);
endchecker

bind signed_non_restoring_divider snrdiv_sva sva (.*);