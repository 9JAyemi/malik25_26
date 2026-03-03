// SVA for ClockDivider
// Bindable checker focusing on correctness, concision, and coverage.

module ClockDivider_sva #(parameter int unsigned Hz = 27000000)
(
  input  logic        clock,
  input  logic        reset,
  input  logic        fastMode,
  input  logic [24:0] counter,
  input  logic        oneHertz_enable
);

  localparam int unsigned W   = 25;
  localparam int unsigned MAX = (1<<W)-1;

  // Parameter sanity
  initial begin
    assert (Hz > 0) else $error("ClockDivider: Hz must be > 0");
    assert (Hz <= MAX) else $error("ClockDivider: Hz (%0d) must fit in %0d bits", Hz, W);
  end

  // Clocking
  default clocking cb @(posedge clock); endclocking

  // Avoid $past at time 0
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clock) past_valid <= 1'b1;

  // Thresholds and mode select (using value sampled on the decision cycle)
  localparam logic [W-1:0] TH_FAST  = 25'd3;
  localparam logic [W-1:0] TH_NORM  = logic[W-1:0]'(Hz);
  let TERM_P = $past(fastMode) ? TH_FAST : TH_NORM;

  // Reset behavior (synchronous)
  assert property (@(posedge clock) reset |=> (counter == '0 && !oneHertz_enable));

  // Disable other properties during reset and before past is valid
  default disable iff (reset || !past_valid);

  // Pulse occurs iff prior cycle met the threshold for the sampled mode
  assert property (oneHertz_enable |->  $past(counter == TERM_P));
  assert property (($past(counter == TERM_P)) |-> (oneHertz_enable && counter == '0));

  // Exactly one-cycle-wide pulse
  assert property (oneHertz_enable |=> !oneHertz_enable);

  // Normal advance when prior cycle did NOT hit the threshold
  assert property ((!$past(counter == TERM_P)) |-> (!oneHertz_enable && counter == $past(counter) + 25'd1));

  // Basic functional coverage
  cover property (@(posedge clock) !reset ##[1:$] oneHertz_enable);                              // see at least one pulse after reset release
  cover property (disable iff (reset || !past_valid) (oneHertz_enable &&  $past(fastMode)));     // fast mode pulse
  cover property (disable iff (reset || !past_valid) (oneHertz_enable && !$past(fastMode)));     // normal mode pulse

endmodule

// Bind into DUT
bind ClockDivider ClockDivider_sva #(.Hz(Hz)) ClockDivider_sva_i
(
  .clock(clock),
  .reset(reset),
  .fastMode(fastMode),
  .counter(counter),
  .oneHertz_enable(oneHertz_enable)
);