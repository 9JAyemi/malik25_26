module my_module_sva (
    input logic Q,
    input logic Q_N,
    input logic CLK,
    input logic D
);

    // Q captures a high D value by the next clock sample.
    check_q_captures_high_d: assert property (
        @(posedge CLK) D |=> Q
    );

    // Q captures a low D value by the next clock sample.
    check_q_captures_low_d: assert property (
        @(posedge CLK) !D |=> !Q
    );

    // Q_N is always the inverse of Q.
    check_qn_inverts_q: assert property (
        @(posedge CLK) Q_N == ~Q
    );

    // Q remains unchanged when D already matches Q.
    check_q_stable_when_d_matches_q: assert property (
        @(posedge CLK) (D == Q) |=> $stable(Q)
    );

    // Q changes when D differs from Q.
    check_q_updates_when_d_differs_q: assert property (
        @(posedge CLK) (D != Q) |=> !$stable(Q)
    );

    // Q_N goes low after a high D value is captured.
    check_qn_after_high_d: assert property (
        @(posedge CLK) D |=> !Q_N
    );

    // Q_N goes high after a low D value is captured.
    check_qn_after_low_d: assert property (
        @(posedge CLK) !D |=> Q_N
    );

endmodule