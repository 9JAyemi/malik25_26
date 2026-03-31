module sky130_fd_sc_ms__a21o_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // X matches the implemented combinational equation.
    check_x_matches_implemented_equation: assert property (
        @(posedge clk)
        X == ((~(A1 & A2)) & (A1 ^ B1)) | ((~B1) & A1)
    );

    // X reduces to B1 OR (A1 & ~A2).
    check_x_simplified_equation: assert property (
        @(posedge clk)
        X == (B1 | (A1 & ~A2))
    );

    // When B1 is low, X must be low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk)
        !B1 |-> !X
    );

    // When B1 is high, X must equal A1.
    check_b1_high_passes_a1: assert property (
        @(posedge clk)
        B1 |-> (X == A1)
    );

    // When A1 is low, X must be low.
    check_a1_low_forces_x_low: assert property (
        @(posedge clk)
        !A1 |-> !X
    );

    // When A1 and A2 are both high, X must be low.
    check_a1_a2_high_block: assert property (
        @(posedge clk)
        (A1 && A2) |-> !X
    );

    // When A1 is high and A2 is low, X must equal B1.
    check_a1_high_a2_low_passes_b1: assert property (
        @(posedge clk)
        (A1 && !A2) |-> (X == B1)
    );

    // When A1 is high and A2 is high, X must be low.
    check_a1_a2_high_block: assert property (
        @(posedge clk)
        (A1 && A2) |-> !X
    );

    // When A1 and A2 are both low, X must equal B1.
    check_a1_a2_low_passes_b1: assert property (
        @(posedge clk)
        (!A1 && !A2) |-> (X == B1)
    );

    // When A1 is low and A2 is high, X must be low.
    check_a1_low_a2_high_block: assert property (
        @(posedge clk)
        (!A1 && A2) |-> !X
    );

endmodule