module d_latch_sva (
    input logic D,
    input logic S,
    input logic R,
    input logic CLK,
    input logic Q
);

    // If R is high at a clock edge, Q is cleared on the next sampled cycle.
    check_reset_clears_q: assert property (
        @(posedge CLK) disable iff (1'b0)
        R |=> (Q == 1'b0)
    );

    // If S is high while R is low, Q is set on the next sampled cycle.
    check_set_sets_q: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!R && S) |=> (Q == 1'b1)
    );

    // If neither R nor S is high, Q captures D on the next sampled cycle.
    check_data_capture: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!R && !S) |=> (Q == $past(D))
    );

    // If both R and S are high, R has priority and Q is cleared.
    check_reset_priority_over_set: assert property (
        @(posedge CLK) disable iff (1'b0)
        (R && S) |=> (Q == 1'b0)
    );

    // On every cycle, Q matches the previous cycle's selected input.
    check_full_next_state_function: assert property (
        @(posedge CLK) disable iff (1'b0)
        1'b1 |=> (Q == ($past(R) ? 1'b0 : ($past(S) ? 1'b1 : $past(D))))
    );

endmodule