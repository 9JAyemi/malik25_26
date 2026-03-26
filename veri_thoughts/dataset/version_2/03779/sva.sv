module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count,
    input logic       overflow
);

    // Reset drives the counter state and overflow low on the next cycle.
    check_reset_clears_state: assert property (
        @(posedge clk) disable iff ($initstate)
        (reset == 1'b1) |=> (count == 4'b0000 && overflow == 1'b0)
    );

    // A non-max count increments by one and keeps overflow low.
    check_increment_path: assert property (
        @(posedge clk) disable iff ($initstate)
        ((reset == 1'b0) && (count != 4'hF)) |=> (count == ($past(count) + 4'd1) && overflow == 1'b0)
    );

    // A max count wraps to zero and raises overflow on the next cycle.
    check_wrap_path: assert property (
        @(posedge clk) disable iff ($initstate)
        ((reset == 1'b0) && (count == 4'hF)) |=> (count == 4'h0 && overflow == 1'b1)
    );

    // Overflow can only be high when the count value is zero.
    check_overflow_implies_zero_count: assert property (
        @(posedge clk) disable iff ($initstate)
        (overflow == 1'b1) |-> (count == 4'h0)
    );

    // Overflow only comes from a non-reset wrap from 4'hF.
    check_overflow_only_after_wrap: assert property (
        @(posedge clk) disable iff ($initstate)
        (overflow == 1'b1) |-> ($past(reset) == 1'b0 && $past(count) == 4'hF)
    );

    // Overflow is a one-cycle pulse.
    check_overflow_single_cycle: assert property (
        @(posedge clk) disable iff ($initstate)
        (overflow == 1'b1) |=> (overflow == 1'b0)
    );

endmodule