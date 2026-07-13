module top_module_sva (
    input logic clk,
    input logic reset,
    input logic up_down,
    input logic [7:0] in_hi,
    input logic [7:0] in_lo,
    input logic [15:0] out
);
    ///// Reset behavior /////
    // On synchronous active-low reset, out equals {in_hi,in_lo}.
    check_reset_out_base: assert property (
        @(posedge clk) (reset == 1'b0) |-> (out == {in_hi, in_lo})
    );

    ///// Functional invariants /////
    // Out minus base is always in [0..7] when not in reset.
    check_delta_range: assert property (
        @(posedge clk) disable iff (!reset) ((out - {in_hi, in_lo}) <= 16'd7)
    );

    // When counting up, next delta = (prev delta + 1) mod 8.
    check_delta_inc_mod8: assert property (
        @(posedge clk) disable iff (!reset)
            (up_down == 1'b1) |=> ((out - {in_hi, in_lo}) == ((($past(out) - $past({in_hi, in_lo})) + 16'd1) & 16'h0007))
    );

    // When counting down, next delta = (prev delta - 1) mod 8.
    check_delta_dec_mod8: assert property (
        @(posedge clk) disable iff (!reset)
            (up_down == 1'b0) |=> ((out - {in_hi, in_lo}) == ((($past(out) - $past({in_hi, in_lo})) + 16'd7) & 16'h0007))
    );

    // Delta (out-base) changes every cycle when not in reset.
    check_delta_changes_every_cycle: assert property (
        @(posedge clk) disable iff (!reset)
            1'b1 |=> ((out - {in_hi, in_lo}) != ($past(out) - $past({in_hi, in_lo})))
    );

    ///// Boundary wrap cases /////
    // If delta is 7 and counting up, next delta becomes 0.
    check_inc_wrap_7_to_0: assert property (
        @(posedge clk) disable iff (!reset)
            (((out - {in_hi, in_lo}) == 16'd7) && (up_down == 1'b1)) |=> ((out - {in_hi, in_lo}) == 16'd0)
    );

    // If delta is 0 and counting down, next delta becomes 7.
    check_dec_wrap_0_to_7: assert property (
        @(posedge clk) disable iff (!reset)
            (((out - {in_hi, in_lo}) == 16'd0) && (up_down == 1'b0)) |=> ((out - {in_hi, in_lo}) == 16'd7)
    );

    // If delta != 7 and counting up, next delta increments by 1.
    check_inc_no_wrap_plus1: assert property (
        @(posedge clk) disable iff (!reset)
            (((out - {in_hi, in_lo}) != 16'd7) && (up_down == 1'b1)) |=> ((out - {in_hi, in_lo}) == (($past(out) - $past({in_hi, in_lo})) + 16'd1))
    );

    // If delta != 0 and counting down, next delta decrements by 1.
    check_dec_no_wrap_minus1: assert property (
        @(posedge clk) disable iff (!reset)
            (((out - {in_hi, in_lo}) != 16'd0) && (up_down == 1'b0)) |=> ((out - {in_hi, in_lo}) == (($past(out) - $past({in_hi, in_lo})) - 16'd1))
    );

    ///// Post-reset first-cycle behavior /////
    // Immediately after reset release, if up, delta becomes 1.
    check_post_reset_release_inc: assert property (
        @(posedge clk) ($past(reset) == 1'b0 && reset == 1'b1 && up_down == 1'b1) |-> ((out - {in_hi, in_lo}) == 16'd1)
    );

    // Immediately after reset release, if down, delta becomes 7.
    check_post_reset_release_dec: assert property (
        @(posedge clk) ($past(reset) == 1'b0 && reset == 1'b1 && up_down == 1'b0) |-> ((out - {in_hi, in_lo}) == 16'd7)
    );
endmodule