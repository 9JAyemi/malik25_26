// SVA for constant_voltage_driver
// Bindable, concise, high-quality checks and coverage

module constant_voltage_driver_sva #(
  parameter int unsigned VOLTAGE_LEVEL = 1800,
  parameter int unsigned RISE_TIME     = 10,
  parameter int unsigned FALL_TIME     = 20,
  parameter int unsigned W_VOUT        = 1
)(
  input  logic                 clk,
  input  logic                 rst,
  input  logic                 ctrl,
  input  logic [W_VOUT-1:0]    vout,
  input  logic [31:0]          rise_counter,
  input  logic [31:0]          fall_counter
);

  // Static sanity checks
  initial begin
    assert (RISE_TIME > 0) else $error("RISE_TIME must be > 0");
    assert (FALL_TIME > 0) else $error("FALL_TIME must be > 0");
    if (VOLTAGE_LEVEL >= (1 << W_VOUT))
      $error("vout width (%0d) too small for voltage_level=%0d (truncation)", W_VOUT, VOLTAGE_LEVEL);
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Helpers
  function automatic int unsigned min_u (int unsigned a, b);
    return (a < b) ? a : b;
  endfunction
  function automatic int unsigned up_val   (int unsigned rc);
    return (min_u(rc, RISE_TIME) * VOLTAGE_LEVEL) / RISE_TIME;
  endfunction
  function automatic int unsigned down_val (int unsigned fc);
    return VOLTAGE_LEVEL - ((min_u(fc, FALL_TIME) * VOLTAGE_LEVEL) / FALL_TIME);
  endfunction

  // Past values with reset-aware history
  let rc_p = $past(rise_counter, 1, rst);
  let fc_p = $past(fall_counter, 1, rst);

  // Reset behavior
  assert property (rst |-> (vout == '0 && rise_counter == 32'd0 && fall_counter == 32'd0));

  // Counter bounds
  assert property (rise_counter <= RISE_TIME);
  assert property (fall_counter <= FALL_TIME);

  // Branch exclusivity/reset of opposite counter
  assert property (ctrl  |-> (fall_counter == 32'd0));
  assert property (!ctrl |-> (rise_counter == 32'd0));

  // Rise counter update and saturation
  assert property (ctrl && (rc_p < RISE_TIME)  |-> (rise_counter == rc_p + 1));
  assert property (ctrl && (rc_p >= RISE_TIME) |-> (rise_counter == rc_p));

  // Fall counter update and saturation
  assert property (!ctrl && (fc_p < FALL_TIME)  |-> (fall_counter == fc_p + 1));
  assert property (!ctrl && (fc_p >= FALL_TIME) |-> (fall_counter == fc_p));

  // vout functional model (note: vout equals truncated expected due to DUT width)
  assert property (ctrl && (rc_p < RISE_TIME)  |-> (vout == up_val(rc_p)[W_VOUT-1:0]));
  assert property (ctrl && (rc_p >= RISE_TIME) |-> (vout == VOLTAGE_LEVEL[W_VOUT-1:0]));

  assert property (!ctrl && (fc_p < FALL_TIME)  |-> (vout == down_val(fc_p)[W_VOUT-1:0]));
  assert property (!ctrl && (fc_p >= FALL_TIME) |-> (vout == '0));

  // No X/Z on key controls/outputs after reset
  assert property (!$isunknown({ctrl, vout}));

  // Targeted coverage
  cover property (ctrl  && (rc_p >= RISE_TIME) && (vout == VOLTAGE_LEVEL[W_VOUT-1:0])); // reached/sustained high
  cover property (!ctrl && (fc_p >= FALL_TIME) && (vout == '0));                        // reached/sustained low

  // Interrupted ramps
  cover property ($past(ctrl,1,rst) && (rc_p > 0) && (rc_p < RISE_TIME) && !ctrl);
  cover property (!$past(ctrl,1,rst) && (fc_p > 0) && (fc_p < FALL_TIME) && ctrl);

endmodule

// Bind into the DUT (inherits instance parameters and widths)
bind constant_voltage_driver
  constant_voltage_driver_sva #(
    .VOLTAGE_LEVEL(voltage_level),
    .RISE_TIME    (rise_time),
    .FALL_TIME    (fall_time),
    .W_VOUT       ($bits(vout))
  ) constant_voltage_driver_sva_i (
    .clk          (clk),
    .rst          (rst),
    .ctrl         (ctrl),
    .vout         (vout),
    .rise_counter (rise_counter),
    .fall_counter (fall_counter)
  );