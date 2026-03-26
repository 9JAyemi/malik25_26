module ff32_en_SIZE13_shift_sva (
    input logic [12:0] D,
    input logic [12:0] Q,
    input logic en,
    input logic clk,
    input logic rst,
    input logic shift
);

    // clk is the sampling clock; rst is active-high.
    // Reset drives Q to zero by the next sampled clock.
    check_reset_clears_q: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |=> (Q == 13'd0)
    );

    // If reset stays asserted across sampled clocks, Q remains zero.
    check_reset_holds_q_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        (rst && $past(rst)) |-> (Q == 13'd0)
    );

    // When shift is high, the visible LSB is the inserted zero bit.
    check_shifted_q_lsb_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        shift |-> (Q[0] == 1'b0)
    );

    // A prior enabled load makes the unshifted view equal to the prior D.
    check_load_unshifted_view: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && $past(en) && !shift) |-> (Q == $past(D))
    );

    // A prior enabled load makes the shifted view equal to the prior D left-shifted by one.
    check_load_shifted_view: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && $past(en) && shift) |-> (Q == {$past(D[11:0]), 1'b0})
    );

    // With no load and shift low on consecutive cycles, Q holds steady.
    check_hold_unshifted_view: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && !$past(en) && !$past(shift) && !shift) |-> (Q == $past(Q))
    );

    // With no load and shift high on consecutive cycles, Q holds steady.
    check_hold_shifted_view: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && !$past(en) && $past(shift) && shift) |-> (Q == $past(Q))
    );

    // With no load, changing shift from low to high left-shifts the visible Q value.
    check_shift_toggle_low_to_high: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && !$past(en) && !$past(shift) && shift) |-> (Q == {$past(Q[11:0]), 1'b0})
    );

    // With no load, changing shift from high to low exposes the prior shifted upper bits.
    check_shift_toggle_high_to_low: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && !$past(en) && $past(shift) && !shift) |-> (Q[11:0] == $past(Q[12:1]))
    );

endmodule