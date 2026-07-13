module shift_register_sva (
    input logic        clk,
    input logic        reset,
    input logic        serial_in,
    input logic        full,
    input logic [7:0]  parallel_out,
    input logic        serial_p,
    input logic        serial_s,
    input logic [3:0]  state,
    input logic [8:0]  shift,
    input logic [10:0] count
);

    // parallel_out reflects the low 8 bits of shift.
    check_parallel_out_mapping: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        parallel_out == shift[7:0]
    );

    // serial_p captures serial_in on each clock.
    check_serial_p_pipeline: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        serial_p == $past(serial_in)
    );

    // serial_s captures serial_p on each clock.
    check_serial_s_pipeline: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        serial_s == $past(serial_p)
    );

    // Synchronous reset returns to idle and clears full.
    check_reset_state_and_full: assert property (
        @(posedge clk)
        reset |=> (state == 4'h0 && full == 1'b0)
    );

    // Idle with a high sampled input stays in state 0 and keeps full low.
    check_idle_hold_without_start: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (state == 4'h0 && serial_s == 1'b1) |=> (state == 4'h0 && full == 1'b0)
    );

    // Idle with a low sampled input starts the sequence and loads 651.
    check_idle_start_transition: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (state == 4'h0 && serial_s == 1'b0) |=> (state == 4'h1 && count == 11'd651 && full == 1'b0)
    );

    // Active states hold state and decrement count while count is nonzero.
    check_active_count_decrement: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ((state inside {4'h1,4'h2,4'h3,4'h4,4'h5,4'h6,4'h7,4'h8,4'h9,4'ha}) && (count != 11'd0))
        |=> (state == $past(state) && count == ($past(count) - 11'd1))
    );

    // Shift stays unchanged during active countdown cycles.
    check_shift_stable_while_counting: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ((state inside {4'h1,4'h2,4'h3,4'h4,4'h5,4'h6,4'h7,4'h8,4'h9,4'ha}) && (count != 11'd0))
        |=> (shift == $past(shift))
    );

    // States 1 through 9 shift in serial_s and advance when count reaches zero.
    check_mid_state_shift_and_advance: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ((state inside {4'h1,4'h2,4'h3,4'h4,4'h5,4'h6,4'h7,4'h8,4'h9}) && (count == 11'd0))
        |=> (state == ($past(state) + 4'h1) &&
             shift == { $past(serial_s), $past(shift[8:1]) } &&
             count == 11'd1302)
    );

    // State a performs the last shift and loads the final 651 count.
    check_last_shift_to_done: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (state == 4'ha && count == 11'd0)
        |=> (state == 4'hb &&
             shift == { $past(serial_s), $past(shift[8:1]) } &&
             count == 11'd651)
    );

    // State b returns to idle and raises full.
    check_done_to_idle_with_full: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (state == 4'hb) |=> (state == 4'h0 && full == 1'b1)
    );

endmodule