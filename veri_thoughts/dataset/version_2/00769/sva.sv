module binary_counter_sva (
    input logic clk,
    input logic en,
    input logic clr,
    input logic [3:0] count
);
    // When clr is 1, next cycle count must be 0.
    check_clear_sets_zero: assert property (
        @(posedge clk) clr |=> (count == 4'b0)
    );

    // Clear has priority over enable when both are 1.
    check_clear_overrides_enable: assert property (
        @(posedge clk) (clr && en) |=> (count == 4'b0)
    );

    // When enabled without clear, count increments by 1 modulo 16.
    check_enable_increments: assert property (
        @(posedge clk) (!clr && en) |=> (count == $past(count) + 4'd1)
    );

    // When both clear and enable are 0, count holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) (!clr && !en) |=> (count == $past(count))
    );

    // When count is 0xF and enabled (without clear), it wraps to 0.
    check_wrap_on_max: assert property (
        @(posedge clk) (!clr && en && (count == 4'hF)) |=> (count == 4'h0)
    );

    // Any change must be due to prior clr or prior enable without clr.
    check_no_spurious_change: assert property (
        @(posedge clk) disable iff ($initstate)
            (count != $past(count)) |-> ($past(clr) || ($past(en) && !$past(clr)))
    );

    // If clr was high in the previous cycle, current count is 0.
    check_prev_clear_results_zero: assert property (
        @(posedge clk) disable iff ($initstate)
            $past(clr) |-> (count == 4'h0)
    );

    // If previously enabled without clear, current count equals prev+1.
    check_prev_enable_increments: assert property (
        @(posedge clk) disable iff ($initstate)
            $past(!clr && en) |-> (count == $past(count) + 4'd1)
    );

    // If previously disabled without clear, current count is unchanged.
    check_prev_hold: assert property (
        @(posedge clk) disable iff ($initstate)
            $past(!clr && !en) |-> (count == $past(count))
    );

    // Functional update equation matches RTL for all cases.
    check_functional_update_equation: assert property (
        @(posedge clk) disable iff ($initstate)
            count == ($past(clr) ? 4'd0 : ($past(en) ? $past(count) + 4'd1 : $past(count)))
    );
endmodule