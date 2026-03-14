module data_flip_flop_sva (
    input logic Q,
    input logic CLK,
    input logic D
);
    // Q equals D from the previous clock edge (1-cycle latency of DFF).
    check_q_captures_prev_d: assert property (
        @(posedge CLK) 1'b1 |=> (Q == $past(D))
    );

    // If D was stable over the last two cycles, Q does not change this cycle.
    check_q_stable_when_d_stable: assert property (
        @(posedge CLK) $past(1'b1,2) && ($past(D) == $past(D,2)) |-> (Q == $past(Q))
    );

    // If D toggled between the last two cycles, Q toggles this cycle.
    check_q_toggles_when_d_toggled: assert property (
        @(posedge CLK) $past(1'b1,2) && ($past(D) != $past(D,2)) |-> (Q != $past(Q))
    );
endmodule