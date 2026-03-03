// SVA checker for var15_multi
// Provide a free-running clk and bind to the DUT.
// Example bind (adjust clk name as needed):
//   bind var15_multi var15_multi_sva u_var15_multi_sva (.clk(tb_clk), .*);

module var15_multi_sva (
  input logic clk,
  input logic A, B, C, D, E, F, G, H, I, J, K, L, M, N, O,
  input logic valid
);

  default clocking cb @(posedge clk); endclocking

  // Past-valid guard for $past usage
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Recompute expected totals (8-bit wrap matches DUT)
  localparam logic [7:0] MIN_VALUE  = 8'd120;
  localparam logic [7:0] MAX_WEIGHT = 8'd60;
  localparam logic [7:0] MAX_VOLUME = 8'd60;

  logic [7:0] v, w, vol;
  assign v =
        A * 8'd4
      + B * 8'd8
      + C * 8'd0
      + D * 8'd20
      + E * 8'd10
      + F * 8'd12
      + G * 8'd18
      + H * 8'd14
      + I * 8'd6
      + J * 8'd15
      + K * 8'd30
      + L * 8'd8
      + M * 8'd16
      + N * 8'd18
      + O * 8'd18;

  assign w =
        A * 8'd28
      + B * 8'd8
      + C * 8'd27
      + D * 8'd18
      + E * 8'd27
      + F * 8'd28
      + G * 8'd6
      + H * 8'd1
      + I * 8'd20
      + J * 8'd0
      + K * 8'd5
      + L * 8'd13
      + M * 8'd8
      + N * 8'd14
      + O * 8'd22;

  assign vol =
        A * 8'd27
      + B * 8'd27
      + C * 8'd4
      + D * 8'd4
      + E * 8'd0
      + F * 8'd24
      + G * 8'd4
      + H * 8'd20
      + I * 8'd12
      + J * 8'd15
      + K * 8'd5
      + L * 8'd2
      + M * 8'd9
      + N * 8'd28
      + O * 8'd19;

  // Pack inputs in deterministic order [0]=A, ... [14]=O
  logic [0:14] sel;
  assign sel = {A,B,C,D,E,F,G,H,I,J,K,L,M,N,O};

  // Coefficient arrays aligned with sel[0]=A ... sel[14]=O
  localparam logic [7:0] VAL_C [0:14] = '{8'd4, 8'd8, 8'd0, 8'd20, 8'd10, 8'd12, 8'd18, 8'd14, 8'd6, 8'd15, 8'd30, 8'd8, 8'd16, 8'd18, 8'd18};
  localparam logic [7:0] W_C   [0:14] = '{8'd28,8'd8, 8'd27,8'd18,8'd27,8'd28,8'd6, 8'd1, 8'd20,8'd0, 8'd5, 8'd13,8'd8, 8'd14,8'd22};
  localparam logic [7:0] VOL_C [0:14] = '{8'd27,8'd27,8'd4, 8'd4, 8'd0, 8'd24,8'd4, 8'd20,8'd12,8'd15,8'd5, 8'd2, 8'd9, 8'd28,8'd19};

  // Knownness
  assert property (!$isunknown({sel,valid}))) else $error("X/Z detected on inputs or valid");

  // Combinational equivalence of valid
  assert property (valid == ((v >= MIN_VALUE) && (w <= MAX_WEIGHT) && (vol <= MAX_VOLUME)))
    else $error("valid does not match constraint function");

  // Valid cannot change if inputs are stable
  assert property (disable iff (!past_valid) $stable(sel) |-> $stable(valid))
    else $error("valid changed while inputs were stable");

  // Monotonicity: adding only items (no 1->0) cannot decrease totals
  assert property (disable iff (!past_valid)
                   ((($past(sel) & ~sel) == '0) && (sel != $past(sel)))
                   |-> (v >= $past(v) && w >= $past(w) && vol >= $past(vol)))
    else $error("Totals decreased when only adding items");

  // Monotonicity: removing only items (no 0->1) cannot increase totals
  assert property (disable iff (!past_valid)
                   (((sel & ~$past(sel)) == '0) && (sel != $past(sel)))
                   |-> (v <= $past(v) && w <= $past(w) && vol <= $past(vol)))
    else $error("Totals increased when only removing items");

  // Exact per-item delta checks on a single-bit toggle (verifies all coefficients)
  logic [0:14] diff;
  assign diff = sel ^ $past(sel);

  genvar i;
  generate
    for (i = 0; i < 15; i++) begin : gen_delta
      // Single 0->1 toggle of item i
      assert property (disable iff (!past_valid)
                       ($rose(sel[i]) && $onehot(diff))
                       |-> (v == ($past(v) + VAL_C[i]) &&
                            w == ($past(w) + W_C[i])   &&
                            vol == ($past(vol) + VOL_C[i])))
        else $error("0->1 delta mismatch for item %0d", i);

      // Single 1->0 toggle of item i
      assert property (disable iff (!past_valid)
                       ($fell(sel[i]) && $onehot(diff))
                       |-> (v == ($past(v) - VAL_C[i]) &&
                            w == ($past(w) - W_C[i])   &&
                            vol == ($past(vol) - VOL_C[i])))
        else $error("1->0 delta mismatch for item %0d", i);
    end
  endgenerate

  // Sanity: all-zero selection must be invalid
  assert property ((sel == '0) |-> !valid)
    else $error("valid asserted with no items selected");

  // Targeted functional coverage
  cover property (valid); // at least one valid configuration observed

  // Boundary hits for each constraint
  cover property ((v == MIN_VALUE) && (w <= MAX_WEIGHT) && (vol <= MAX_VOLUME));
  cover property ((v >= MIN_VALUE) && (w == MAX_WEIGHT) && (vol <= MAX_VOLUME));
  cover property ((v >= MIN_VALUE) && (w <= MAX_WEIGHT) && (vol == MAX_VOLUME));

  // Single-constraint failures (to ensure tests exercise each cause of invalid)
  cover property ((v <  MIN_VALUE) && (w <= MAX_WEIGHT) && (vol <= MAX_VOLUME));
  cover property ((v >= MIN_VALUE) && (w >  MAX_WEIGHT) && (vol <= MAX_VOLUME));
  cover property ((v >= MIN_VALUE) && (w <= MAX_WEIGHT) && (vol >  MAX_VOLUME));

  // Exercise all-zero selection
  cover property (sel == '0);

endmodule