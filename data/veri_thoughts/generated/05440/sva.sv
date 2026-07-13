module score_counter_sva (
    input logic        clk,
    input logic        reset,
    input logic        d_inc,
    input logic        d_dec,
    input logic        d_clr,
    input logic [3:0]  dig0,
    input logic [3:0]  dig1
);

    // A sampled reset drives both digits to zero by the following cycle.
    check_reset_clears_digits: assert property (
        @(posedge clk)
        reset |=> (dig0 == 4'd0 && dig1 == 4'd0)
    );

    // Clear forces both digits to zero on the next cycle.
    check_clear_sets_zero: assert property (
        @(posedge clk) disable iff (reset)
        d_clr |=> (dig0 == 4'd0 && dig1 == 4'd0)
    );

    // With no command asserted, the displayed value holds.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (reset)
        (!d_clr && !d_inc && !d_dec) |=> (dig0 == $past(dig0) && dig1 == $past(dig1))
    );

    // Increment without carry increases only the ones digit.
    check_inc_without_carry: assert property (
        @(posedge clk) disable iff (reset)
        (!d_clr && d_inc && (dig0 < 4'd9)) |=> (dig0 == ($past(dig0) + 4'd1) && dig1 == $past(dig1))
    );

    // Increment at x9 carries into the tens digit.
    check_inc_with_carry: assert property (
        @(posedge clk) disable iff (reset)
        (!d_clr && d_inc && (dig0 == 4'd9) && (dig1 < 4'd9)) |=> (dig0 == 4'd0 && dig1 == ($past(dig1) + 4'd1))
    );

    // Increment at 99 wraps the count to 00.
    check_inc_wraps_99_to_00: assert property (
        @(posedge clk) disable iff (reset)
        (!d_clr && d_inc && (dig0 == 4'd9) && (dig1 == 4'd9)) |=> (dig0 == 4'd0 && dig1 == 4'd0)
    );

    // Decrement from 00 or 01 clamps the value to 10.
    check_dec_floor_to_ten: assert property (
        @(posedge clk) disable iff (reset)
        (!d_clr && !d_inc && d_dec && (dig1 == 4'd0) && (dig0 < 4'd2)) |=> (dig0 == 4'd0 && dig1 == 4'd1)
    );

    // Decrement from x1 borrows and produces x-1,9.
    check_dec_borrow_from_x1: assert property (
        @(posedge clk) disable iff (reset)
        (!d_clr && !d_inc && d_dec && (dig1 > 4'd0) && (dig0 == 4'd1)) |=> (dig0 == 4'd9 && dig1 == ($past(dig1) - 4'd1))
    );

    // Decrement from x0 borrows and produces x-1,8.
    check_dec_borrow_from_x0: assert property (
        @(posedge clk) disable iff (reset)
        (!d_clr && !d_inc && d_dec && (dig1 > 4'd0) && (dig0 == 4'd0)) |=> (dig0 == 4'd8 && dig1 == ($past(dig1) - 4'd1))
    );

    // All other decrement cases subtract two from the ones digit.
    check_dec_subtracts_two: assert property (
        @(posedge clk) disable iff (reset)
        (!d_clr && !d_inc && d_dec &&
         !((dig1 == 4'd0) && (dig0 < 4'd2)) &&
         !((dig1 > 4'd0) && (dig0 == 4'd1)) &&
         !((dig1 > 4'd0) && (dig0 == 4'd0)))
        |=> (dig0 == ($past(dig0) - 4'd2) && dig1 == $past(dig1))
    );

endmodule