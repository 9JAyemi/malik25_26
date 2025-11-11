// SVA for kb_code: concise, high-quality checks and coverage.
// Bind this file to the DUT.

module kb_code_sva #(parameter logic [7:0] BRK = 8'hF0)
(
  input logic              clk,
  input logic              reset,          // async to flop, sync to SVA clock
  input logic              scan_done_tick,
  input logic [7:0]        scan_out,
  input logic              got_code_tick,
  input logic              state_reg       // DUT internal
);

  localparam logic wait_brk = 1'b0;
  localparam logic get_code = 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic sanity
  a_state_known:    assert property (! $isunknown(state_reg));
  a_tick_known:     assert property (! $isunknown(got_code_tick));
  a_state_legal:    assert property (state_reg inside {wait_brk, get_code});

  // Reset behavior (checked while reset=1)
  a_reset_state:    assert property (@(posedge clk) disable iff (1'b0)
                                     reset |-> (state_reg==wait_brk && !got_code_tick));

  // Wait state: only BRK on scan_done_tick moves to get_code; otherwise hold and never tick
  a_wait_to_get:    assert property ((state_reg==wait_brk && scan_done_tick && scan_out==BRK)
                                     |=> state_reg==get_code);
  a_wait_hold:      assert property ((state_reg==wait_brk && !(scan_done_tick && (scan_out==BRK)))
                                     |=> state_reg==wait_brk);
  a_no_tick_in_wait:assert property ((state_reg==wait_brk) |-> !got_code_tick);

  // No spurious get_code entry without BRK event
  a_no_get_wo_brk:  assert property ($rose(state_reg) |-> $past(scan_done_tick && (scan_out==BRK)));

  // get_code state behavior
  a_get_hold_no_sd: assert property ((state_reg==get_code && !scan_done_tick)
                                     |=> (state_reg==get_code && !got_code_tick));
  a_get_fire_sd:    assert property ((state_reg==get_code && scan_done_tick)
                                     |-> (got_code_tick ##1 state_reg==wait_brk));

  // got_code_tick correctness
  a_tick_when:      assert property (got_code_tick |-> (state_reg==get_code && scan_done_tick));
  a_tick_pulse1:    assert property (got_code_tick |=> !got_code_tick);

  // Functional cover: key scenarios
  // BRK recognized then later a tick generates and returns to wait
  c_brk_then_tick:  cover property ((state_reg==wait_brk && scan_done_tick && scan_out==BRK)
                                    ##1 state_reg==get_code
                                    ##[1:$] (scan_done_tick && got_code_tick)
                                    ##1 state_reg==wait_brk);

  // Ignore non-BRK bytes in wait_brk
  c_ignore_non_brk: cover property (state_reg==wait_brk && scan_done_tick && (scan_out!=BRK)
                                    ##1 state_reg==wait_brk);

  // Back-to-back sequences of BRK->tick
  c_two_seq:        cover property ((state_reg==wait_brk && scan_done_tick && scan_out==BRK)
                                    ##1 state_reg==get_code
                                    ##[1:$] (scan_done_tick && got_code_tick)
                                    ##1 state_reg==wait_brk
                                    ##[1:$] (scan_done_tick && scan_out==BRK)
                                    ##1 state_reg==get_code
                                    ##[1:$] (scan_done_tick && got_code_tick)
                                    ##1 state_reg==wait_brk);

endmodule

// Bind to DUT (state_reg is internal to kb_code)
bind kb_code kb_code_sva #(.BRK(8'hF0)) kb_code_sva_i
(
  .clk(clk),
  .reset(reset),
  .scan_done_tick(scan_done_tick),
  .scan_out(scan_out),
  .got_code_tick(got_code_tick),
  .state_reg(state_reg)
);