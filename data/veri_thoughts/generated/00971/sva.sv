module top_module_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] A,
    input logic [3:0] final_output
);
    ///// Reset behavior /////
    // While reset is LOW, final_output equals A + 3 (counter held at 0).
    check_reset_low_output_eq_A_plus3: assert property (
        @(posedge clk) (!reset) |-> (final_output == (A + 4'd3))
    );

    // While reset is LOW and A is stable, final_output remains stable.
    check_reset_low_stableA_output_stable: assert property (
        @(posedge clk) (!reset && $stable(A)) |-> $stable(final_output)
    );

    // On reset deassertion edge, final_output equals A + 3.
    check_reset_release_output_eq_A_plus3: assert property (
        @(posedge clk) $rose(reset) |-> (final_output == (A + 4'd3))
    );

    ///// Functional behavior with counter /////
    // With A stable across cycles, final_output advances by $past(enable) (mod 16).
    check_step_with_stableA_prev_enable: assert property (
        @(posedge clk) disable iff (!reset)
            $past(reset) && (A == $past(A))
            |-> final_output == ($past(final_output) + ($past(enable) ? 4'd1 : 4'd0))
    );

    // General delta: if previous enable was 0, delta(final_output) equals delta(A) (mod 16).
    check_delta_with_prev_enable0: assert property (
        @(posedge clk) disable iff (!reset)
            $past(reset) && ($past(enable) == 1'b0)
            |-> final_output == ($past(final_output) + (A + (~$past(A) + 4'd1)))
    );

    // General delta: if previous enable was 1, delta(final_output) equals delta(A)+1 (mod 16).
    check_delta_with_prev_enable1: assert property (
        @(posedge clk) disable iff (!reset)
            $past(reset) && ($past(enable) == 1'b1)
            |-> final_output == ($past(final_output) + (A + (~$past(A) + 4'd1)) + 4'd1)
    );

    // Over two cycles with A stable and enable HIGH in both, final_output increases by 2 (mod 16).
    check_two_cycle_inc_enable_high_stable_A: assert property (
        @(posedge clk) disable iff (!reset)
            $past(reset,2) &&
            (A == $past(A)) && ($past(A) == $past(A,2)) &&
            $past(enable) && $past(enable,2)
            |-> final_output == ($past(final_output,2) + 4'd2)
    );

    // Over two cycles with A stable and enable LOW in both, final_output holds.
    check_two_cycle_hold_enable_low_stable_A: assert property (
        @(posedge clk) disable iff (!reset)
            $past(reset,2) &&
            (A == $past(A)) && ($past(A) == $past(A,2)) &&
            !$past(enable) && !$past(enable,2)
            |-> final_output == $past(final_output,2)
    );
endmodule