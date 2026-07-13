module mux2to1_sva (
    input logic A,
    input logic B,
    input logic sel,
    input logic reset,   // active-LOW asynchronous reset
    input logic clk,
    input logic out
);

    // Output must be 0 whenever reset is asserted (active-low).
    check_reset_forces_out_low: assert property (
        @(posedge clk) (!reset) |-> (out == 1'b0)
    );

    // On the cycle immediately following a cycle in reset, out must still be 0.
    check_out_zero_after_reset_cycle: assert property (
        @(posedge clk) $past(!reset) |-> (out == 1'b0)
    );

    // The previous cycle's registered value matches the RTL branch taken that cycle.
    check_prev_cycle_assignment_matches_rtl: assert property (
        @(posedge clk) disable iff (!reset)
            !$initstate |-> (
                $past(out) ==
                ($past(reset) ? ($past(sel) ? $past(B) : $past(A)) : 1'b0)
            )
    );

    // When last cycle was not in reset and sel==0, last out equals last A.
    check_prev_cycle_sel0_path: assert property (
        @(posedge clk) disable iff (!reset)
            (!$initstate && $past(reset) && ($past(sel) == 1'b0)) |-> ($past(out) == $past(A))
    );

    // When last cycle was not in reset and sel==1, last out equals last B.
    check_prev_cycle_sel1_path: assert property (
        @(posedge clk) disable iff (!reset)
            (!$initstate && $past(reset) && ($past(sel) == 1'b1)) |-> ($past(out) == $past(B))
    );

    // When last cycle was in reset, last out equals 0.
    check_prev_cycle_reset_path: assert property (
        @(posedge clk) disable iff (!reset)
            (!$initstate && !$past(reset)) |-> ($past(out) == 1'b0)
    );

endmodule