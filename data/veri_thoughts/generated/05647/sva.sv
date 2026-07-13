module d_latch_sva (
    input logic D,
    input logic C,
    input logic Q
);

    // Q holds the D value sampled on the previous rising edge of C.
    check_q_captures_previous_d: assert property (
        @(posedge C) 1'b1 |=> (Q == $past(D))
    );

    // If D is unchanged across two rising edges, Q matches D at the later edge.
    check_q_matches_stable_d: assert property (
        @(posedge C) 1'b1 |=> (($past(D) == D) -> (Q == D))
    );

    // If D changes between rising edges, Q is not transparent to the new D value.
    check_q_is_edge_triggered: assert property (
        @(posedge C) 1'b1 |=> (($past(D) != D) -> (Q != D))
    );

endmodule