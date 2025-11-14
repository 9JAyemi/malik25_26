// SVA for axi_timer. Bind this module to the DUT.
// Focused, high-quality checks + essential functional coverage.

module axi_timer_sva #(
  parameter int WIDTH = 8,
  parameter int MAX_VALUE = 256
)(
  input  logic                 clk,
  input  logic                 rst,
  input  logic                 load,
  input  logic [WIDTH-1:0]     value,
  input  logic                 enable,
  input  logic                 timer_expired,
  input  logic [WIDTH-1:0]     current_value
);

  // Clocking/past-valid
  default clocking cb @(posedge clk); endclocking
  logic past_valid;
  initial past_valid = 0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Fit MAX_VALUE into WIDTH; also keep a sanity check
  localparam logic [WIDTH-1:0] MAX_FIT = MAX_VALUE[WIDTH-1:0];
  initial assert (MAX_VALUE < (1<<WIDTH))
    else $error("axi_timer: MAX_VALUE (%0d) must be < 2**WIDTH (%0d)", MAX_VALUE, 1<<WIDTH);

  // 1) Reset behavior (synchronous, highest priority)
  assert property (past_valid && $past(rst)
                   |-> current_value == '0 && timer_expired == 1'b0);

  // 2) Load behavior (takes priority over enable), timer_expired unchanged
  assert property (past_valid && $past(!rst && load)
                   |-> current_value == $past(value) && timer_expired == $past(timer_expired));

  // 3) Hold when idle (no rst, no load, no enable)
  assert property (past_valid && $past(!rst && !load && !enable)
                   |-> current_value == $past(current_value) && timer_expired == $past(timer_expired));

  // 4) Decrement on enable when previous value != 0, and timer_expired must be 0
  assert property (past_valid && $past(!rst && !load && enable) && ($past(current_value) != '0)
                   |-> current_value == $past(current_value) - 1 && timer_expired == 1'b0);

  // 5) Expire on enable when previous value == 0: reload to MAX_FIT and assert timer_expired
  assert property (past_valid && $past(!rst && !load && enable) && ($past(current_value) == '0)
                   |-> current_value == MAX_FIT && timer_expired == 1'b1);

  // 6) timer_expired can only change on rst or enable (load/idle must hold it)
  assert property (past_valid && $past(!rst && !enable)
                   |-> timer_expired == $past(timer_expired));

  // 7) When load and enable both 1, load wins (redundant with #2 but explicit)
  assert property (past_valid && $past(!rst && load && enable)
                   |-> current_value == $past(value));

  // 8) If continuously enabled, timer_expired pulse width is one cycle
  assert property (past_valid &&
                   $past(!rst && !load && enable) && ($past(current_value) == '0) ##1
                   (!rst && !load && enable) |-> timer_expired == 1'b0);

  // Optional: no X on outputs after first cycle
  assert property (past_valid |-> !$isunknown({timer_expired, current_value}));

  // ----------------
  // Functional coverage (key scenarios)
  // ----------------

  // C1: Load then decrement at least once
  cover property (past_valid && $past(!rst && load) ##1 (!rst && !load && enable) &&
                  (current_value == $past(value) - 1));

  // C2: Wrap/expire: enable on zero causes reload to MAX_FIT and timer_expired high
  cover property (past_valid && $past(!rst && !load && enable) && ($past(current_value) == '0)
                  ##1 (current_value == MAX_FIT && timer_expired));

  // C3: Idle hold for multiple cycles
  cover property (past_valid && $past(!rst && !load && !enable)[*2]
                  ##1 (current_value == $past(current_value)));

  // C4: Load has priority over enable
  cover property (past_valid && $past(!rst && load && enable)
                  ##1 (current_value == $past(value)));

  // C5: Countdown to an expire pulse under continuous enable after a nonzero load
  cover property (disable iff (rst)
                  load && (value > 2) ##1
                  (enable && !load)[*1:$] ##1 timer_expired);

endmodule

// Example bind (place in a testbench or a separate bind file):
// bind axi_timer axi_timer_sva #(.WIDTH(WIDTH), .MAX_VALUE(MAX_VALUE))
//   axi_timer_sva_i(.clk(clk), .rst(rst), .load(load), .value(value),
//                   .enable(enable), .timer_expired(timer_expired),
//                   .current_value(current_value));