// SVA for RoundSaturation
// Bind this to the DUT. Focused, high-signal-quality checks with key corner coverage.

bind RoundSaturation RoundSaturation_SVA #(.IB(IB), .FB(FB)) u_roundsat_sva (
  .in(in),
  .out(out),
  .in_val(in_val),
  .round_val(round_val),
  .max_val(max_val),
  .min_val(min_val)
);

module RoundSaturation_SVA #(parameter int IB = 4, FB = 8)
(
  input  logic signed [IB+FB-1:0] in,
  input  logic signed [IB+FB-1:0] out,

  // internal DUT wires (checked for self-consistency)
  input  logic signed [IB+FB-1:0] in_val,
  input  logic signed [IB+FB-1:0] round_val,
  input  logic signed [IB+FB-1:0] max_val,
  input  logic signed [IB+FB-1:0] min_val
);

  localparam int W = IB+FB;

  default clocking cb @($global_clock); endclocking

  // Constants (signed)
  localparam logic signed [W-1:0] CALC_MAX = (logic signed [W-1:0])((1 <<< (W-1)) - 1);
  localparam logic signed [W-1:0] CALC_MIN = - (logic signed [W-1:0])(1 <<< (W-1));
  localparam logic [W-1:0]        MASK     = (FB > 0) ? ((1 <<< FB) - 1) : '0;
  localparam logic signed [W-1:0] HALF     = (FB > 0) ? (1 <<< (FB-1))   : '0;

  function automatic logic signed [W-1:0] sat(input logic signed [W-1:0] x);
    if (x > CALC_MAX) return CALC_MAX;
    else if (x < CALC_MIN) return CALC_MIN;
    else return x;
  endfunction

  function automatic logic signed [W-1:0] round_model(input logic signed [W-1:0] x);
    // mathematically correct: add/sub half then arithmetic shift right
    logic signed [W-1:0] t;
    t = x + ((x >= 0) ? HALF : -HALF);
    return t >>> FB;
  endfunction

  // Basic sanity: parameters, known values
  initial begin
    assert (IB > 0 && FB > 0) else $error("IB and FB must be > 0");
  end
  assert property (!$isunknown(in) && !$isunknown(out));

  // Internal constants correctness
  assert property (max_val == CALC_MAX);
  assert property (min_val == CALC_MIN);

  // Input scaling check (use a shift for independence)
  assert property (in_val == (in <<< FB));

  // Rounding correctness (arithmetic, sign-aware)
  assert property (round_val == round_model(in_val));

  // Saturation correctness
  assert property (
    out == ((round_val > CALC_MAX) ? CALC_MAX :
           ((round_val < CALC_MIN) ? CALC_MIN : round_val))
  );

  // End-to-end check from input only (independent model)
  assert property (out == sat(round_model(in <<< FB)));

  // Range invariant and idempotent saturation
  assert property (out inside {[CALC_MIN:CALC_MAX]});
  assert property (sat(out) == out);

  // Boundary implications
  assert property ((round_val >  CALC_MAX) |-> (out == CALC_MAX));
  assert property ((round_val <  CALC_MIN) |-> (out == CALC_MIN));
  assert property ((round_val == CALC_MAX) |-> (out == CALC_MAX));
  assert property ((round_val == CALC_MIN) |-> (out == CALC_MIN));

  // Monotonicity: non-decreasing transfer
  assert property (($past(in) <= in) |-> ($past(out) <= out));

  // Coverage: key corners and ties
  cover property (out == CALC_MAX);
  cover property (out == CALC_MIN);
  cover property (in == '0 && out == '0);

  // Ties at exactly half LSB (positive and negative), measured on in_val
  // Tie when abs(in_val[FB-1:0]) == HALF
  cover property (FB > 0 && (in_val >= 0) && ((in_val & MASK) == HALF));
  cover property (FB > 0 && (in_val <  0) && (((-in_val) & MASK) == HALF));

  // Near-saturation rounding (just over/under the bound before clamp)
  cover property ((round_val > CALC_MAX) && (out == CALC_MAX));
  cover property ((round_val < CALC_MIN) && (out == CALC_MIN));

endmodule