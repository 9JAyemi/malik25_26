module my_dff_reset_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic RESET_B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // A sampled reset-low cycle forces Q low by the next sampled clock.
    check_q_low_after_sampled_reset: assert property (
        @(posedge CLK)
        (!$initstate && !$past(RESET_B)) |-> (Q == 1'b0)
    );

    // On the first active clock after reset, Q is still low before loading D.
    check_q_low_on_reset_release: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (!$initstate && !$past(RESET_B)) |-> (Q == 1'b0)
    );

    // A high Q on an active clock implies reset was high on the prior sample.
    check_q_high_requires_prior_reset_high: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (!$initstate && Q) |-> $past(RESET_B)
    );

endmodule