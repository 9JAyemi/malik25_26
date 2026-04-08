module sky130_fd_sc_hdll__a222oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2
);

    // Y must match the implemented NAND-AND logic function.
    check_y_matches_logic: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == (~(A1 & A2) & ~(B1 & B2) & ~(C1 & C2))
    );

    // A high-high condition on the A pair forces Y low.
    check_a_pair_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 & A2) |-> ~Y
    );

    // A high-high condition on the B pair forces Y low.
    check_b_pair_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (B1 & B2) |-> ~Y
    );

    // A high-high condition on the C pair forces Y low.
    check_c_pair_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (C1 & C2) |-> ~Y
    );

    // If no input pair is simultaneously high, Y must be high.
    check_no_pair_active_gives_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (~(A1 & A2) & ~(B1 & B2) & ~(C1 & C2)) |-> Y
    );

    // A high Y implies none of the three input pairs are simultaneously high.
    check_y_high_implies_no_active_pair: assert property (
        @(posedge clk) disable iff (1'b0)
        Y |-> (~(A1 & A2) & ~(B1 & B2) & ~(C1 & C2))
    );

    // A low Y implies at least one input pair is simultaneously high.
    check_y_low_implies_some_active_pair: assert property (
        @(posedge clk) disable iff (1'b0)
        ~Y |-> ((A1 & A2) | (B1 & B2) | (C1 & C2))
    );

endmodule