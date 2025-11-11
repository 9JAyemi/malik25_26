// SVA for aurora_201_CHANNEL_ERROR_DETECT
// Bind-ready, concise, full functional checks + key coverage

module aurora_201_CHANNEL_ERROR_DETECT_sva (
  input  logic USER_CLK,
  input  logic SOFT_ERROR,
  input  logic HARD_ERROR,
  input  logic LANE_UP,
  input  logic POWER_DOWN,
  input  logic CHANNEL_SOFT_ERROR,
  input  logic CHANNEL_HARD_ERROR,
  input  logic RESET_CHANNEL
);

  default clocking cb @(posedge USER_CLK); endclocking

  // Warm-up to safely use $past
  logic warm1, warm2;
  always_ff @(posedge USER_CLK) begin
    warm1 <= 1'b1;
    warm2 <= warm1;
  end

  // Knownness (avoid X/Z propagation after warm-up)
  assert property (disable iff (!warm1) !$isunknown({LANE_UP, POWER_DOWN}));
  assert property (disable iff (!warm2) !$isunknown({SOFT_ERROR, HARD_ERROR,
                                                    CHANNEL_SOFT_ERROR, CHANNEL_HARD_ERROR,
                                                    RESET_CHANNEL}));

  // Functional correctness
  // Two-cycle pipeline from SOFT/HARD_ERROR to CHANNEL_*_ERROR
  assert property (disable iff (!warm2) CHANNEL_SOFT_ERROR == $past(SOFT_ERROR, 2));
  assert property (disable iff (!warm2) CHANNEL_HARD_ERROR == $past(HARD_ERROR, 2));

  // One-cycle registered OR for RESET_CHANNEL
  assert property (disable iff (!warm1) RESET_CHANNEL == $past((!LANE_UP) || POWER_DOWN));

  // Minimal but meaningful coverage
  cover property ($rose(SOFT_ERROR) ##2 CHANNEL_SOFT_ERROR);
  cover property ($fell(SOFT_ERROR) ##2 !CHANNEL_SOFT_ERROR);

  cover property ($rose(HARD_ERROR) ##2 CHANNEL_HARD_ERROR);
  cover property ($fell(HARD_ERROR) ##2 !CHANNEL_HARD_ERROR);

  cover property ($rose(POWER_DOWN) ##1 RESET_CHANNEL);
  cover property ($fell(POWER_DOWN) && LANE_UP ##1 !RESET_CHANNEL);

  cover property ($fell(LANE_UP) ##1 RESET_CHANNEL);
  cover property ($rose(LANE_UP) && !POWER_DOWN ##1 !RESET_CHANNEL);

endmodule

// Bind into the DUT
bind aurora_201_CHANNEL_ERROR_DETECT aurora_201_CHANNEL_ERROR_DETECT_sva sva_i (
  .USER_CLK(USER_CLK),
  .SOFT_ERROR(SOFT_ERROR),
  .HARD_ERROR(HARD_ERROR),
  .LANE_UP(LANE_UP),
  .POWER_DOWN(POWER_DOWN),
  .CHANNEL_SOFT_ERROR(CHANNEL_SOFT_ERROR),
  .CHANNEL_HARD_ERROR(CHANNEL_HARD_ERROR),
  .RESET_CHANNEL(RESET_CHANNEL)
);