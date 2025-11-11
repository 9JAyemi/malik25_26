// SVA for debounce_switch
// Bind this file to the DUT:
// bind debounce_switch debounce_switch_sva #(.WIDTH(WIDTH), .N(N), .RATE(RATE)) sva_i();

module debounce_switch_sva #(
  parameter int WIDTH = 1,
  parameter int N     = 3,
  parameter int RATE  = 125000
) ();

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Parameter/sizing sanity
  initial begin
    assert (WIDTH >= 1) else $error("WIDTH must be >=1");
    assert (N >= 2)      else $error("N must be >=2 (shift uses [N-2:0])");
    assert (RATE < (1<<24)) else $error("RATE must fit 24-bit cnt_reg");
  end

  // Asynchronous reset behavior
  a_async_cnt_reset  : assert property (@(posedge rst) cnt_reg == 24'd0);
  a_async_state_reset: assert property (@(posedge rst) state == {WIDTH{1'b0}});
  genvar r;
  generate for (r=0; r<WIDTH; r++) begin
    a_async_deb_reset: assert property (@(posedge rst) debounce_reg[r] == {N{1'b0}});
  end endgenerate

  // Basic wiring
  a_out_eq_state: assert property (out == state);

  // Counter correctness
  a_cnt_bound: assert property (cnt_reg <= RATE);
  a_cnt_inc  : assert property ((cnt_reg < RATE) |=> cnt_reg == $past(cnt_reg) + 24'd1);
  a_cnt_wrap : assert property ((cnt_reg == RATE) |=> cnt_reg == 24'd0);
  a_cnt_no_x : assert property (!$isunknown(cnt_reg));

  // Debounce shift and state machine per bit
  genvar k;
  generate for (k=0; k<WIDTH; k++) begin : per_bit
    // Shift happens only when cnt_reg == 0
    let shift_in(d, b) = {d[N-2:0], b};

    a_shift_on_zero   : assert property ((cnt_reg == 24'd0) |=> debounce_reg[k] == shift_in($past(debounce_reg[k]), $past(in[k])));
    a_hold_when_count : assert property ((cnt_reg != 24'd0) |=> $stable(debounce_reg[k]));

    // State decoding: all-0 -> 0, all-1 -> 1, otherwise hold
    a_state_to_0: assert property ((~|debounce_reg[k]) |=> state[k] == 1'b0);
    a_state_to_1: assert property ((&debounce_reg[k])  |=> state[k] == 1'b1);
    a_state_hold: assert property (((|debounce_reg[k]) && !(&debounce_reg[k])) |=> state[k] == $past(state[k]));

    // State changes only when window is uniform in prior cycle
    a_rise_only_all1s: assert property ($rose(state[k]) |-> $past(&debounce_reg[k]));
    a_fall_only_all0s: assert property ($fell(state[k]) |-> $past(~|debounce_reg[k]));

    // No X/Z on outputs/state
    a_no_x_out  : assert property (!$isunknown(out[k]));
    a_no_x_state: assert property (!$isunknown(state[k]));

    // Functional coverage
    c_state_rise: cover property ($rose(state[k]));
    c_state_fall: cover property ($fell(state[k]));
    c_all1_seen : cover property (&debounce_reg[k]);
    c_all0_seen : cover property (~|debounce_reg[k]);
  end endgenerate

  // Counter coverage
  c_shift_pulse: cover property (cnt_reg == 24'd0);
  c_wrap       : cover property ($past(cnt_reg) == RATE && cnt_reg == 24'd0);

endmodule