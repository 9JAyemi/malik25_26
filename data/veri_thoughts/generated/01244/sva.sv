module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] Q
);
    ///// Reset behavior /////
    // If reset is held across two clock edges, Q must be 0 on the later edge.
    reset_held_forces_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (Q == 4'b0000)
    );
    // If reset is held across two clock edges, Q must remain stable.
    reset_hold_stable: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (Q == $past(Q))
    );
    // On the first cycle after reset was high, the sampled Q must be 0.
    post_reset_sample_zero: assert property (
        @(posedge clk) ($past(reset) && !reset) |-> (Q == 4'b0000)
    );

    ///// Counting behavior /////
    // When not in reset for consecutive cycles, Q increments by 1 (mod-16).
    increment_each_cycle_no_reset: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (Q == ($past(Q) + 4'd1))
    );
    // Over two consecutive non-reset cycles, Q advances by 2 (mod-16).
    increment_over_two_cycles: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset,2) && $past(!reset)) |-> (Q == ($past(Q,2) + 4'd2))
    );
    // Wrap from 0xF to 0x0 when running.
    wrap_from_f_to_0: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && ($past(Q) == 4'hF)) |-> (Q == 4'h0)
    );
    // If Q is 0 while running, the previous value must have been 0xF.
    zero_only_from_wrap_no_reset: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && (Q == 4'h0)) |-> ($past(Q) == 4'hF)
    );
    // While running, Q changes every cycle.
    changes_every_cycle_no_reset: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (Q != $past(Q))
    );
endmodule