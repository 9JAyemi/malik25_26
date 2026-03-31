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

    // A sampled reset cycle leaves Q low on the next clock.
    check_reset_cycle_clears_q: assert property (
        @(posedge C) !R |=> (Q == 1'b0)
    );

    // With reset inactive, Q captures D on the next clock.
    check_capture_d_when_reset_inactive: assert property (
        @(posedge C) disable iff (!R) 1'b1 |=> (Q == $past(D))
    );

    // With reset inactive, a high D is captured into Q.
    check_capture_high_d: assert property (
        @(posedge C) disable iff (!R) D |=> (Q == 1'b1)
    );

    // With reset inactive, a low D is captured into Q.
    check_capture_low_d: assert property (
        @(posedge C) disable iff (!R) !D |=> (Q == 1'b0)
    );

    // A sampled high D is reflected on Q on the next clock.
    check_high_d_sampled_on_next_cycle: assert property (
        @(posedge C) disable iff (!R) D |=> (Q == 1'b1)
    );

    // A sampled low D is reflected on Q on the next clock.
    check_low_d_sampled_on_next_cycle: assert property (
        @(posedge C) disable iff (!R) !D |=> (Q == 1'b0)
    );

endmodule