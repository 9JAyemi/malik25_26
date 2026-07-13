module bitwise_and_assert (
    input logic a,
    input logic b,
    input logic reset,
    input logic clk,
    input logic out
);
    // While reset is LOW, out is forced to 0.
    check_reset_forces_out_zero: assert property (
        @(posedge clk) !reset |-> (out == 1'b0)
    );

    // On reset deassertion (LOW->HIGH), out remains 0 in that sampled cycle.
    check_out_zero_on_reset_release: assert property (
        @(posedge clk) $rose(reset) |-> (out == 1'b0)
    );

    // With reset HIGH in consecutive cycles, out equals previous cycle's a & b.
    check_sync_update_matches_prev_and: assert property (
        @(posedge clk) disable iff (!reset) $past(reset) |-> (out === $past(a & b))
    );

    // If previous a and b were 1 with reset HIGH, out becomes 1.
    check_prev_inputs_one_implies_out_one: assert property (
        @(posedge clk) disable iff (!reset) $past(reset) && $past(a) && $past(b) |-> (out == 1'b1)
    );

    // If either previous a or b was 0 with reset HIGH, out becomes 0.
    check_prev_inputs_zero_implies_out_zero: assert property (
        @(posedge clk) disable iff (!reset) $past(reset) && ((!$past(a)) || (!$past(b))) |-> (out == 1'b0)
    );

    // A rise on out requires previous a & b to be 1 and reset HIGH previously.
    check_out_rise_requires_prev_and_one: assert property (
        @(posedge clk) disable iff (!reset) $rose(out) |-> ($past(reset) && ($past(a & b) === 1'b1))
    );
endmodule