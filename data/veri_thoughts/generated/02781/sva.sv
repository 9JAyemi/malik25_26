module rcv_sva (
    input logic clk,
    input logic reset,
    input logic full,
    input logic [7:0] parallel_out,
    input logic serial_in,
    // Internal signals from rcv
    input logic serial_p,
    input logic serial_s,
    input logic [3:0] state,
    input logic [8:0] shift,
    input logic [10:0] count
);
    // Serial pipeline: serial_p captures serial_in with 1-cycle latency.
    check_serial_p_d1: assert property (
        @(posedge clk) disable iff (reset) serial_p == $past(serial_in, 1, reset)
    );

    // Serial pipeline: serial_s captures serial_p with 1-cycle latency.
    check_serial_s_d1: assert property (
        @(posedge clk) disable iff (reset) serial_s == $past(serial_p, 1, reset)
    );

    // parallel_out directly reflects shift[7:0].
    check_parallel_out_matches_shift: assert property (
        @(posedge clk) disable iff (reset) parallel_out == shift[7:0]
    );

    // On reset deassertion, state becomes 0 and full becomes 0.
    check_reset_clears_state_full: assert property (
        @(posedge clk) disable iff (reset) $past(reset) |-> (state == 4'h0) && (full == 1'b0)
    );

    // In IDLE (state=0) with start detected (serial_s=0), next state=1 and count loads 651.
    check_start_detect_transition: assert property (
        @(posedge clk) disable iff (reset) (state == 4'h0 && serial_s == 1'b0) |=> (state == 4'h1 && count == 11'd651)
    );

    // In IDLE (state=0) with no start (serial_s=1), hold state and count.
    check_idle_holds_state_and_count: assert property (
        @(posedge clk) disable iff (reset) (state == 4'h0 && serial_s == 1'b1) |=> (state == 4'h0 && count == $past(count))
    );

    // While in IDLE (state=0), full is driven low on the next cycle.
    check_idle_drives_full_low: assert property (
        @(posedge clk) disable iff (reset) (state == 4'h0) |=> (full == 1'b0)
    );

    // When state reaches 0xb, next cycle goes to IDLE and full pulses high.
    check_state_b_to_idle_and_full: assert property (
        @(posedge clk) disable iff (reset) (state == 4'hb) |=> (state == 4'h0 && full == 1'b1)
    );

    // In busy states (!0 and !0xb) with count!=0, decrement count; hold state and shift.
    check_count_down_and_hold: assert property (
        @(posedge clk) disable iff (reset)
            (state != 4'h0 && state != 4'hb && count != 11'd0)
            |=> (count == $past(count) - 11'd1) && (state == $past(state)) && (shift == $past(shift))
    );

    // In busy states (!0 and !0xb) with count==0, advance state, shift in serial_s, and reload count to 1302.
    check_advance_and_shift_on_count_zero: assert property (
        @(posedge clk) disable iff (reset)
            (state != 4'h0 && state != 4'hb && count == 11'd0)
            |=> (state == $past(state) + 4'd1) && (shift == { $past(serial_s), $past(shift[8:1]) }) && (count == 11'd1302)
    );

    // full is a single-cycle pulse.
    check_full_single_cycle: assert property (
        @(posedge clk) disable iff (reset) full |=> !full
    );

    // full can only be asserted following state==0xb.
    check_full_only_after_state_b: assert property (
        @(posedge clk) disable iff (reset) full |-> ($past(state, 1, reset) == 4'hb)
    );
endmodule