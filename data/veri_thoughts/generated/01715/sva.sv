module d_ff_sva (
    input logic D,
    input logic CLK,
    input logic Q,
    input logic QN
);
    // Analysis: Clock = CLK (posedge). No reset present. Sequential logic: Q<=D, QN<=~D on posedge.

    // Q equals D from the previous clock edge (one-cycle latency).
    check_q_follows_d_next: assert property (
        @(posedge CLK) 1'b1 |=> (Q == $past(D))
    );

    // QN equals ~D from the previous clock edge (one-cycle latency).
    check_qn_follows_notd_next: assert property (
        @(posedge CLK) 1'b1 |=> (QN == ~($past(D)))
    );

    // QN is the complement of Q (checked from the second edge onward).
    check_outputs_complement_next: assert property (
        @(posedge CLK) 1'b1 |=> (QN == ~Q)
    );

    // Q and QN are never equal (checked from the second edge onward).
    check_outputs_mutex_next: assert property (
        @(posedge CLK) 1'b1 |=> (Q ^ QN)
    );

    // If D rises at a clock, Q is 1 on the next clock.
    check_d_rise_sets_q_next: assert property (
        @(posedge CLK) $rose(D) |=> (Q == 1'b1)
    );

    // If D falls at a clock, Q is 0 on the next clock.
    check_d_fall_clears_q_next: assert property (
        @(posedge CLK) $fell(D) |=> (Q == 1'b0)
    );

    // If D is 1 at a clock, QN is 0 on the next clock.
    check_d1_drives_qn0_next: assert property (
        @(posedge CLK) (D == 1'b1) |=> (QN == 1'b0)
    );

    // If D is 0 at a clock, QN is 1 on the next clock.
    check_d0_drives_qn1_next: assert property (
        @(posedge CLK) (D == 1'b0) |=> (QN == 1'b1)
    );
endmodule