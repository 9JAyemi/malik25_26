module sky130_fd_sc_hvl__a21oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // DUT is combinational; clk is an external sampling clock and there is no reset.

    // Y matches the implemented AOI21 boolean function.
    check_boolean_function: assert property (
        @(posedge clk) Y == ~(B1 | (A1 & A2))
    );

    // A high B1 input forces Y low.
    check_b1_forces_y_low: assert property (
        @(posedge clk) B1 |-> ~Y
    );

    // High A1 and A2 force the AND term high and drive Y low.
    check_and_term_forces_y_low: assert property (
        @(posedge clk) (A1 & A2) |-> ~Y
    );

    // When B1 is low, Y reduces to the inverse of A1&A2.
    check_b1_low_reduces_to_nand: assert property (
        @(posedge clk) (~B1) |-> (Y == ~(A1 & A2))
    );

    // A high output requires B1 to be low.
    check_y_high_requires_b1_low: assert property (
        @(posedge clk) Y |-> ~B1
    );

    // A high output requires the A1/A2 AND term to be low.
    check_y_high_requires_and_term_low: assert property (
        @(posedge clk) Y |-> (~A1 | ~A2)
    );

    // A low output must be caused by B1 or the A1/A2 AND term being high.
    check_y_low_has_valid_cause: assert property (
        @(posedge clk) (~Y) |-> (B1 | (A1 & A2))
    );

endmodule