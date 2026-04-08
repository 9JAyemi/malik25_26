module sky130_fd_sc_ls__a31o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // No RTL clock or reset exists; sample assertions on the formal global clock.

    // X must match the implemented OR-of-ANDs function.
    check_x_matches_rtl_function: assert property (
        @($global_clock) disable iff (1'b0)
        X === (((A1 & A2) | (A3 & B1)) ? 1'b1 : 1'b0)
    );

    // A1 and A2 high must drive X high.
    check_a1_a2_term_drives_high: assert property (
        @($global_clock) disable iff (1'b0)
        (A1 & A2) |-> (X === 1'b1)
    );

    // A3 and B1 high must drive X high.
    check_a3_b1_term_drives_high: assert property (
        @($global_clock) disable iff (1'b0)
        (A3 & B1) |-> (X === 1'b1)
    );

    // With both product terms low, X must be low.
    check_no_product_term_drives_low: assert property (
        @($global_clock) disable iff (1'b0)
        !((A1 & A2) | (A3 & B1)) |-> (X === 1'b0)
    );

    // A high X must be caused by at least one product term.
    check_high_x_has_active_product_term: assert property (
        @($global_clock) disable iff (1'b0)
        (X === 1'b1) |-> (((A1 & A2) | (A3 & B1)) === 1'b1)
    );

    // If X is high without the A1/A2 term, the A3/B1 term must be high.
    check_high_x_without_a1a2_requires_a3b1: assert property (
        @($global_clock) disable iff (1'b0)
        ((X === 1'b1) && ((A1 & A2) !== 1'b1)) |-> ((A3 & B1) === 1'b1)
    );

    // If X is high without the A3/B1 term, the A1/A2 term must be high.
    check_high_x_without_a3b1_requires_a1a2: assert property (
        @($global_clock) disable iff (1'b0)
        ((X === 1'b1) && ((A3 & B1) !== 1'b1)) |-> ((A1 & A2) === 1'b1)
    );

endmodule