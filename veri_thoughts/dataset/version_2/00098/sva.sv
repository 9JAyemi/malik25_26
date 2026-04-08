module dff_sva (
    input logic D,
    input logic CLK,
    input logic Q
);

    // Q reflects D sampled on the previous rising clock edge.
    check_q_matches_previous_d: assert property (
        @(posedge CLK) disable iff (1'b0) (!$initstate) |-> (Q == $past(D))
    );

    // A sampled high D is captured into Q on the next rising edge.
    check_high_d_captured: assert property (
        @(posedge CLK) disable iff (1'b0) D |=> Q
    );

    // A sampled low D is captured into Q on the next rising edge.
    check_low_d_captured: assert property (
        @(posedge CLK) disable iff (1'b0) !D |=> !Q
    );

    // If D is stable across clock edges, Q stays stable on the following edge.
    check_stable_d_keeps_q_stable: assert property (
        @(posedge CLK) disable iff (1'b0) (!$initstate && $stable(D)) |=> $stable(Q)
    );

    // If D changes across clock edges, Q changes on the following edge.
    check_changed_d_changes_q: assert property (
        @(posedge CLK) disable iff (1'b0) (!$initstate && !$stable(D)) |=> !$stable(Q)
    );

endmodule