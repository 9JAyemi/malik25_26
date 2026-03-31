module dffr_sva #(
    parameter [0:0] INIT = 1'b0
) (
    input logic Q,
    input logic D,
    input logic C,
    input logic R
);

    // Active-low reset forces Q low.
    check_reset_forces_q_low: assert property (
        @(posedge C) !R |-> (Q == 1'b0)
    );

    // A sampled reset cycle leaves Q low on the next clock sample.
    check_reset_cycle_keeps_q_low: assert property (
        @(posedge C) (!R ##1 R) |-> (Q == 1'b0)
    );

    // With reset inactive, Q matches the previous cycle's D value.
    check_q_follows_previous_d: assert property (
        @(posedge C) disable iff (!R) 1'b1 |=> (Q == $past(D))
    );

    // A high Q must come from a prior D value of 1.
    check_q_high_requires_prior_d_high: assert property (
        @(posedge C) disable iff (!R) Q |-> $past(D)
    );

    // A low Q must come from a prior D value of 0.
    check_q_low_requires_prior_d_low: assert property (
        @(posedge C) disable iff (!R) !Q |-> !$past(D)
    );

endmodule