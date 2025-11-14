// SVA for binary_counter. Bind this module to the DUT.
// Focus: state transitions, count behavior, reset semantics, and corner cases.
module binary_counter_sva #(
  parameter WIDTH = 4
) (
  input  logic                  clk,
  input  logic                  reset,       // active-low
  input  logic                  count_up,
  input  logic                  count_down,
  input  logic [WIDTH-1:0]      count_out,
  input  logic [1:0]            state_reg
);

  localparam [1:0] INIT       = 2'b00;
  localparam [1:0] COUNT_UP   = 2'b01;
  localparam [1:0] COUNT_DOWN = 2'b10;
  localparam [1:0] RESET_ST   = 2'b11;

  localparam [WIDTH-1:0] MINV = '0;
  localparam [WIDTH-1:0] MAXV = {WIDTH{1'b1}};

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset);

  // Asynchronous reset: state must go to INIT immediately on negedge reset.
  a_async_state_init: assert property (@(negedge reset) ##0 (state_reg == INIT));

  // While reset low at a clock edge, outputs should be zero (INIT drives 0).
  a_reset_zero_out:  assert property (@(posedge clk) !reset |-> (count_out == MINV));

  // No X/Z on key state/outputs in normal operation.
  a_no_x:             assert property (!$isunknown({state_reg, count_out}));

  // Valid state encoding; RESET_ST should be unreachable in this design.
  a_valid_state:      assert property (state_reg inside {INIT, COUNT_UP, COUNT_DOWN, RESET_ST});
  a_never_reset_st:   assert property (state_reg != RESET_ST);

  // INIT drives zero at next cycle.
  a_init_zero_next:   assert property ($past(state_reg) == INIT |-> count_out == MINV);

  // INIT next-state decisions (count_up wins over count_down).
  a_init_to_up:       assert property (state_reg == INIT && count_up            |=> state_reg == COUNT_UP);
  a_init_to_down:     assert property (state_reg == INIT && !count_up && count_down |=> state_reg == COUNT_DOWN);
  a_init_hold:        assert property (state_reg == INIT && !count_up && !count_down |=> state_reg == INIT);

  // COUNT_UP: count increments every cycle (wraps naturally by width).
  a_up_step:          assert property (state_reg == COUNT_UP |=> count_out == $past(count_out) + 1'b1);

  // COUNT_DOWN: count decrements every cycle (wraps naturally by width).
  a_down_step:        assert property (state_reg == COUNT_DOWN |=> count_out == $past(count_out) - 1'b1);

  // COUNT_UP next-state policy.
  a_up_stays_on_up:   assert property ($past(state_reg) == COUNT_UP &&  $past(count_up)                         |-> state_reg == COUNT_UP);
  a_up_exit_on_max:   assert property ($past(state_reg) == COUNT_UP && !$past(count_up) && $past(count_out)==MAXV |-> state_reg == INIT);
  a_up_hold_else:     assert property ($past(state_reg) == COUNT_UP && !$past(count_up) && $past(count_out)!=MAXV |-> state_reg == COUNT_UP);

  // COUNT_DOWN next-state policy.
  a_down_stays_on_down: assert property ($past(state_reg) == COUNT_DOWN &&  $past(count_down)                         |-> state_reg == COUNT_DOWN);
  a_down_exit_on_min:   assert property ($past(state_reg) == COUNT_DOWN && !$past(count_down) && $past(count_out)==MINV |-> state_reg == INIT);
  a_down_hold_else:     assert property ($past(state_reg) == COUNT_DOWN && !$past(count_down) && $past(count_out)!=MINV |-> state_reg == COUNT_DOWN);

  // Coverage: reach modes, wrap-around behavior, and exit conditions.
  c_reach_up:         cover property (state_reg == COUNT_UP);
  c_reach_down:       cover property (state_reg == COUNT_DOWN);

  // Wrap in UP when count_up held high.
  c_up_wrap:          cover property ($past(state_reg) == COUNT_UP && $past(count_up) &&
                                      $past(count_out) == MAXV && state_reg == COUNT_UP && count_out == MINV);

  // Wrap in DOWN when count_down held high.
  c_down_wrap:        cover property ($past(state_reg) == COUNT_DOWN && $past(count_down) &&
                                      $past(count_out) == MINV && state_reg == COUNT_DOWN && count_out == MAXV);

  // Exit to INIT at boundaries when deasserting enables.
  c_up_exit_on_max:   cover property ($past(state_reg) == COUNT_UP && !$past(count_up) &&
                                      $past(count_out) == MAXV && state_reg == INIT);
  c_down_exit_on_min: cover property ($past(state_reg) == COUNT_DOWN && !$past(count_down) &&
                                      $past(count_out) == MINV && state_reg == INIT);

  // INIT tie: both inputs high -> choose COUNT_UP.
  c_init_both_high_choose_up: cover property (state_reg == INIT && count_up && count_down |=> state_reg == COUNT_UP);

  // After reset release, next clock drives output to zero.
  c_reset_release_zero: cover property ($rose(reset) ##1 (count_out == MINV));

endmodule

// Bind example (place in a separate file or a package that sees the DUT symbol):
// bind binary_counter binary_counter_sva #(.WIDTH(WIDTH)) u_sva (.*,.state_reg(state_reg));