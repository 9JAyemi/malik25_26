module counter_mux_xor_sva (
    input logic clk,
    input logic reset,          // synchronous active-high reset
    input logic [3:0] mux_in1,
    input logic [3:0] mux_in2,
    input logic select,
    input logic [3:0] out,
    // Internal RTL signals (bind hierarchically)
    input logic [3:0] count,
    input logic [3:0] mux_out
);

    ///// Counter behavior /////
    // On a reset cycle, count becomes 0 on the next clock.
    reset_clears_count_next: assert property (
        @(posedge clk) reset |=> (count == 4'h0)
    );

    // While reset is held for multiple cycles, count stays 0.
    count_zero_while_reset: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (count == 4'h0)
    );

    // After reset deasserts, count advances from 0 to 1.
    count_is_one_after_release: assert property (
        @(posedge clk) disable iff (reset) ($past(reset) && !reset) |-> (count == 4'h1)
    );

    // When not in reset and not wrapping, count increments by 1.
    count_increments_no_wrap: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(count) != 4'hF)) |-> (count == $past(count) + 4'd1)
    );

    // When not in reset and at max, count wraps to 0.
    count_wrap_after_max: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    ///// Multiplexer behavior /////
    // With select=0, mux_out equals mux_in1.
    mux_sel0_out_eq_in1: assert property (
        @(posedge clk) disable iff (reset) (!select |-> (mux_out == mux_in1))
    );

    // With select=1, mux_out equals mux_in2.
    mux_sel1_out_eq_in2: assert property (
        @(posedge clk) disable iff (reset) (select |-> (mux_out == mux_in2))
    );

    // If both mux inputs are equal, mux_out equals that value regardless of select.
    mux_equal_inputs_passthrough: assert property (
        @(posedge clk) disable iff (reset) (mux_in1 == mux_in2) |-> (mux_out == mux_in1)
    );

    // If select and both inputs are stable, mux_out is stable.
    mux_out_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (reset) ($stable(select) && $stable(mux_in1) && $stable(mux_in2)) |-> $stable(mux_out)
    );

    ///// XOR behavior /////
    // out equals count XOR mux_out.
    out_is_xor_of_count_and_mux: assert property (
        @(posedge clk) disable iff (reset) (out == (count ^ mux_out))
    );

    // If mux_out is zero, out equals count.
    out_equals_count_when_mux_zero: assert property (
        @(posedge clk) disable iff (reset) (mux_out == 4'h0) |-> (out == count)
    );

    // If mux_out is all ones, out is bitwise NOT of count.
    out_equals_not_count_when_mux_all_ones: assert property (
        @(posedge clk) disable iff (reset) (mux_out == 4'hF) |-> (out == ~count)
    );

    // If count and mux_out are stable, out is stable.
    out_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (reset) ($stable(count) && $stable(mux_out)) |-> $stable(out)
    );

endmodule