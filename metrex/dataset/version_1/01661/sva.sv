// SVA checker for tx_run_length_limiter
// Bindable, concise, focuses on functional intent and key invariants

module tx_run_length_limiter_sva #(
  parameter int LANE_WIDTH  = 64,
  parameter int GRANULARITY = 4,
  parameter int RUN_LIMIT   = 85
)(
  input  logic                   clk,
  input  logic                   res_n,
  input  logic                   enable,
  input  logic [LANE_WIDTH-1:0]  data_in,
  input  logic [LANE_WIDTH-1:0]  data_out,
  input  logic                   rf_bit_flip
);

  default clocking cb @(posedge clk); endclocking

  // Threshold matches DUT expression
  localparam int REM_BITS = (LANE_WIDTH % GRANULARITY);
  localparam int THR = RUN_LIMIT - (GRANULARITY-1) - (REM_BITS ? (REM_BITS-1) : (GRANULARITY-1));

  // Helper: run-length from LSB upward (current word)
  function automatic int unsigned runlen_lsb (input logic [LANE_WIDTH-1:0] v);
    int i; int unsigned r; r = 1;
    for (i = 1; i < LANE_WIDTH; i++) begin
      if (v[i] == v[0]) r++; else break;
    end
    return r;
  endfunction

  // Helper: run-length ending at MSB downward (current word)
  function automatic int unsigned runlen_msb (input logic [LANE_WIDTH-1:0] v);
    int i; int unsigned r; r = 1;
    for (i = LANE_WIDTH-2; i >= 0; i--) begin
      if (v[i] == v[LANE_WIDTH-1]) r++; else break;
    end
    return r;
  endfunction

  // Reference accumulator for run ending at MSB across cycles
  int unsigned acc_msb_run;
  logic        past_valid;

  always_ff @(posedge clk) begin
    if (!res_n) begin
      acc_msb_run <= '0;
      past_valid  <= 1'b0;
    end else begin
      past_valid  <= 1'b1;
      automatic int unsigned msb_this = runlen_msb(data_in);
      if (msb_this == LANE_WIDTH)
        acc_msb_run <= acc_msb_run + LANE_WIDTH;
      else
        acc_msb_run <= msb_this;
    end
  end

  // Combinational boundary run estimate (matches intent of DUT)
  function automatic int unsigned boundary_run_len();
    automatic int unsigned lsb_len = runlen_lsb(data_in);
    automatic int unsigned prev_acc = $past(acc_msb_run);
    boundary_run_len = lsb_len
                     + ((past_valid && (data_in[0] == $past(data_in[LANE_WIDTH-1])))
                        ? (prev_acc == 0 ? 1 : prev_acc) : 0);
  endfunction

  // Reset behavior
  property p_reset_outputs_zero;
    !res_n |-> (data_out == '0 && rf_bit_flip == 1'b0);
  endproperty
  assert property (p_reset_outputs_zero);

  // No X on key outputs after reset
  property p_no_x_after_reset;
    disable iff (!res_n) !$isunknown({data_out, rf_bit_flip});
  endproperty
  assert property (p_no_x_after_reset);

  // Pass-through when disabled
  property p_passthrough_when_disabled;
    !enable |-> (data_out == data_in);
  endproperty
  assert property (p_passthrough_when_disabled);

  // If output differs from input, it must be an LSB-only flip and enable must be high
  property p_only_lsb_changes_when_diff;
    (data_out != data_in)
      |-> (enable
           && data_out[LANE_WIDTH-1:1] == data_in[LANE_WIDTH-1:1]
           && data_out[0] == ~data_in[0]);
  endproperty
  assert property (p_only_lsb_changes_when_diff);

  // Flag sets when flip happens
  property p_flag_sets_on_flip;
    (enable && (data_out[0] != data_in[0])) |-> rf_bit_flip;
  endproperty
  assert property (p_flag_sets_on_flip);

  // Flag is sticky when no flip (never changes unless a flip occurs or reset)
  property p_flag_sticky_no_flip;
    disable iff (!res_n) (data_out == data_in) |-> $stable(rf_bit_flip);
  endproperty
  assert property (p_flag_sticky_no_flip);

  // Must flip when boundary run exceeds threshold
  property p_must_flip_when_exceeds;
    disable iff (!res_n)
    (enable && past_valid && (boundary_run_len() > THR))
      |-> (data_out[LANE_WIDTH-1:1] == data_in[LANE_WIDTH-1:1]
           && data_out[0] == ~data_in[0]
           && rf_bit_flip);
  endproperty
  assert property (p_must_flip_when_exceeds);

  // Must not flip when within threshold (or no past available)
  property p_must_not_flip_when_within;
    disable iff (!res_n)
    (enable && (!past_valid || (boundary_run_len() <= THR)))
      |-> (data_out == data_in);
  endproperty
  assert property (p_must_not_flip_when_within);

  // Minimal coverage
  cover property (enable && past_valid && (boundary_run_len() > THR));      // flip condition seen
  cover property (enable && (data_out != data_in));                          // flip occurred
  cover property (enable && (data_out == data_in));                          // no flip path
  cover property (enable && past_valid && (boundary_run_len() == THR));      // edge case

endmodule

// Bind into DUT
bind tx_run_length_limiter
  tx_run_length_limiter_sva #(
    .LANE_WIDTH(LANE_WIDTH),
    .GRANULARITY(GRANULARITY),
    .RUN_LIMIT(RUN_LIMIT)
  ) i_tx_run_length_limiter_sva (
    .clk(clk),
    .res_n(res_n),
    .enable(enable),
    .data_in(data_in),
    .data_out(data_out),
    .rf_bit_flip(rf_bit_flip)
  );