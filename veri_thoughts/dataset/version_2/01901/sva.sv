module pipeline_module_sva (
    input logic clk,
    input logic in,
    input logic out
);

    ///// Pipeline behavior /////
    // Output equals input from two cycles earlier.
    check_out_two_cycle_delay: assert property (
        @(posedge clk) out == $past(in, 2)
    );

    // Previous cycle's output equals input from three cycles earlier.
    check_prev_out_three_cycle_in: assert property (
        @(posedge clk) $past(out, 1) == $past(in, 3)
    );

    // A change on input propagates to output exactly two cycles later.
    check_input_change_propagates_2cycles: assert property (
        @(posedge clk) $changed(in) |-> ##2 $changed(out)
    );

    // An output change implies the input changed two cycles earlier.
    check_out_change_implies_in_change_2cycles_earlier: assert property (
        @(posedge clk) $changed(out) |-> ($past(in, 2) != $past(in, 3))
    );

    // Output change iff the input (two cycles earlier) changed vs three cycles earlier.
    check_out_change_matches_past_in_change: assert property (
        @(posedge clk) $changed(out) == $changed($past(in, 2))
    );

    // If input was same in the prior two cycles, output holds its value this cycle.
    check_equal_in_last_two_cycles_impl_out_stable: assert property (
        @(posedge clk) ($past(in, 1) == $past(in, 2)) |-> (out == $past(out, 1))
    );

    // If input differed in the prior two cycles, output changes this cycle.
    check_inequal_in_last_two_cycles_impl_out_change: assert property (
        @(posedge clk) ($past(in, 1) != $past(in, 2)) |-> (out != $past(out, 1))
    );

    // If output is stable this cycle, input was stable two and three cycles earlier.
    check_out_stable_reflects_past_in_stable: assert property (
        @(posedge clk) $stable(out) |-> ($past(in, 2) == $past(in, 3))
    );

endmodule