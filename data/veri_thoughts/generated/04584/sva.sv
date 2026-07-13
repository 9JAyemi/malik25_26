module my_d_latch_sva (
    input logic D,
    input logic Q,
    input logic GATE
);

    // Q reflects the D value sampled on the previous GATE rise.
    check_q_tracks_previous_d: assert property (
        @(posedge GATE) 1'b1 |=> (Q === $past(D))
    );

    // A sampled high on D is observed as high on Q by the next GATE rise.
    check_q_captures_high_d: assert property (
        @(posedge GATE) (D === 1'b1) |=> (Q === 1'b1)
    );

    // A sampled low on D is observed as low on Q by the next GATE rise.
    check_q_captures_low_d: assert property (
        @(posedge GATE) (D === 1'b0) |=> (Q === 1'b0)
    );

endmodule