module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic Cin,
    input logic [15:0] final_output
);

    // Clock: clk
    // Reset: reset is active high
    // Logic: sequential square-wave select with combinational arithmetic

    // While reset is high, the square-wave select is forced low, so the B path is chosen.
    check_reset_selects_b_path: assert property (
        @(posedge clk)
        reset |-> (final_output == (B + B + Cin))
    );

    // On the sampled cycle where reset is released, the B path is still chosen.
    check_release_cycle_selects_b_path: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $fell(reset)) |-> (final_output == (B + B + Cin))
    );

    // One cycle after reset release, the B path is still chosen.
    check_next_cycle_after_release_selects_b_path: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $fell(reset)) |=> (final_output == (B + B + Cin))
    );

    // The output must always match one of the two implemented arithmetic branch results.
    check_output_matches_a_or_b_path: assert property (
        @(posedge clk) disable iff (reset)
        ((final_output == (A + A + Cin)) || (final_output == (B + B + Cin)))
    );

    // When A equals B, both branches collapse to the same result.
    check_equal_inputs_collapse_paths: assert property (
        @(posedge clk) disable iff (reset)
        (A == B) |-> (final_output == (A + A + Cin))
    );

    // Doubling either selected operand makes the output LSB match Cin.
    check_output_lsb_tracks_cin: assert property (
        @(posedge clk) disable iff (reset)
        (final_output[0] == Cin)
    );

    // With stable equal inputs, the output must remain stable across cycles.
    check_stable_equal_inputs_hold_output: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $stable(A) && $stable(B) && $stable(Cin) && (A == B)) |-> $stable(final_output)
    );

    // With stable inputs, any output change must be a swap between the two branch results.
    check_output_change_with_stable_inputs_swaps_path: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $stable(A) && $stable(B) && $stable(Cin) && $changed(final_output)) |->
        (((final_output == (A + A + Cin)) && ($past(final_output) == (B + B + Cin))) ||
         ((final_output == (B + B + Cin)) && ($past(final_output) == (A + A + Cin))))
    );

endmodule