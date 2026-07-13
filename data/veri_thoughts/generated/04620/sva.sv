module sky130_fd_sc_ls__o21ai_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic Y,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // Y matches the RTL equation each sampled cycle.
    check_y_matches_rtl_equation: assert property (
        @(posedge clk)
        Y == ((A1 ^ A2) ? ~B1 : ((A1 & A2) ? B1 : (A1 & A2)))
    );

    // When A1 and A2 differ, Y is the inverse of B1.
    check_y_inverts_b1_when_a_inputs_differ: assert property (
        @(posedge clk)
        (A1 ^ A2) |-> (Y == ~B1)
    );

    // When A1 and A2 are both high, Y follows B1.
    check_y_follows_b1_when_a_inputs_high: assert property (
        @(posedge clk)
        (A1 & A2) |-> (Y == B1)
    );

    // When A1 and A2 are both low, Y is low.
    check_y_low_when_a_inputs_low: assert property (
        @(posedge clk)
        (!A1 && !A2) |-> (Y == 1'b0)
    );

    // With B1 high, Y reduces to A1 and A2.
    check_y_equals_and_when_b1_high: assert property (
        @(posedge clk)
        B1 |-> (Y == (A1 & A2))
    );

    // With B1 low, Y reduces to A1 xor A2.
    check_y_equals_xor_when_b1_low: assert property (
        @(posedge clk)
        !B1 |-> (Y == (A1 ^ A2))
    );

endmodule