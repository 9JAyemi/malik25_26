// SVA for assert_change_assert
// Bind these assertions to the DUT. Concise, focuses on key state/control, counters, sampling, xz gating, and essential coverage.

module assert_change_assert_sva_bind
(
  input logic                clk, reset_n, start_event, xzcheck_enable,
  input logic [31:0]         window,
  input logic                ignore_new_start, reset_on_new_start, error_on_new_start,
  input logic                pass,
  input logic [width-1:0]    test_expr,
  // Internals
  input logic [width-1:0]    test_expr_reg,
  input logic [31:0]         window_count,
  input logic [31:0]         start_event_count,
  input logic [31:0]         reset_event_count,
  input logic [31:0]         error_event_count,
  input logic [31:0]         xzcheck_event_count,
  input logic [31:0]         xz_error_count,
  input logic [31:0]         xz_ignore_count,
  input logic [31:0]         xz_pass_count,
  input logic [31:0]         xz_reset_count,
  input logic [1:0]          state,
  input logic [1:0]          xz_state,
  input logic [width-1:0]    xz_value,
  input logic [width-1:0]    xz_mask,
  input logic [width-1:0]    xz_error_mask,
  input logic [width-1:0]    xz_ignore_mask,
  input logic [width-1:0]    xz_pass_mask,
  input logic [width-1:0]    xz_reset_mask
);
  parameter int width = 8;

  localparam logic [1:0] IDLE=2'b00, IGNORE=2'b01, CHECK=2'b10, ERROR=2'b11;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n)

  let in_nonidle = (state!=IDLE);
  let xz_active  = (state==CHECK && !start_event && (window_count < window) && xzcheck_enable);

  // Basic legality and pass output
  assert property (state inside {IDLE,IGNORE,CHECK,ERROR});
  assert property (xz_state inside {2'b00,2'b01,2'b10});
  assert property (pass == (state==CHECK));

  // IDLE start behavior
  assert property (state==IDLE && start_event &&  ignore_new_start |=> state==IGNORE);
  assert property (state==IDLE && start_event && !ignore_new_start |=> state==CHECK);

  // New start in non-IDLE
  assert property (in_nonidle && start_event &&  reset_on_new_start |=> state==IDLE && reset_event_count==$past(reset_event_count)+1);
  assert property (in_nonidle && start_event && !reset_on_new_start && error_on_new_start |=> state==ERROR && error_event_count==$past(error_event_count)+1);

  // start_event_count accounting
  assert property (start_event |=> start_event_count==$past(start_event_count)+1);
  assert property (!start_event |=> start_event_count==$past(start_event_count));

  // Counters and window behavior
  assert property (in_nonidle && !start_event |=> window_count==$past(window_count)+1);
  assert property ((state==IDLE) || start_event |=> window_count==$past(window_count));
  assert property (in_nonidle && !start_event && (window_count>=window) |=> state==IDLE);

  // No reset/error event counts on IDLE start
  assert property (state==IDLE && start_event |=> reset_event_count==$past(reset_event_count) && error_event_count==$past(error_event_count));

  // test_expr sampling and hold
  assert property (state==IDLE |=> test_expr_reg==$past(test_expr));
  assert property (state!=IDLE |-> $stable(test_expr_reg));

  // CHECK behavior when xzcheck disabled
  assert property (state==CHECK && !start_event && (window_count<window) && !xzcheck_enable && (test_expr_reg === '0) |=> state==ERROR);
  assert property (state==CHECK && !start_event && (window_count<window) && !xzcheck_enable && !(test_expr_reg === '0) |=> state==CHECK);

  // xz* signals only change when xz_active
  assert property (!xz_active |-> $stable({xz_state, xz_value, xz_mask, xz_error_mask, xz_ignore_mask, xz_pass_mask, xz_reset_mask,
                                           xzcheck_event_count, xz_error_count, xz_ignore_count, xz_pass_count, xz_reset_count}));

  // Monotonic counts (allow wrap implicitly)
  assert property ($rose(reset_n) |-> 1); // anchor after reset release
  assert property (xzcheck_event_count >= $past(xzcheck_event_count));
  assert property (xz_error_count   >= $past(xz_error_count));
  assert property (xz_ignore_count  >= $past(xz_ignore_count));
  assert property (xz_pass_count    >= $past(xz_pass_count));
  assert property (xz_reset_count   >= $past(xz_reset_count));

  // Coverage
  cover property (state==IDLE ##1 (state==CHECK));
  cover property (state==IDLE && start_event && ignore_new_start ##1 state==IGNORE);
  cover property (state==IGNORE && start_event && reset_on_new_start ##1 state==IDLE);
  cover property (state==IGNORE && start_event && !reset_on_new_start && error_on_new_start ##1 state==ERROR);
  cover property (state==CHECK && !start_event && (window_count<window) && !xzcheck_enable && (test_expr_reg==='0) ##1 state==ERROR);
  cover property (state==CHECK && !start_event && (window_count>=window) ##1 state==IDLE);
  cover property (xz_active && xz_state==2'b00 ##1 xz_active && xz_state==2'b01);
  cover property (xz_active && xz_state==2'b01 ##1 xz_active && xz_state==2'b10);
  cover property ($changed(xz_pass_count));
  cover property ($changed(xz_reset_count));
  cover property ($changed(xz_error_count));
  cover property (pass);

endmodule

// Bind to DUT (ports are matched by name to access internals)
bind assert_change_assert assert_change_assert_sva_bind #(.width(width)) (.*);