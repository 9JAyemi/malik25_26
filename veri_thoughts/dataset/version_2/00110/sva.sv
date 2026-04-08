module four_to_one_circuit_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X matches the RTL boolean equation.
    check_output_matches_boolean_equation: assert property (
        @(posedge clk)
        X == ~(((~A1) & (~A2) & (~B1) & B2) | (A1 & A2 & (~B1) & (~B2)))
    );

    // The first product term forces X low.
    check_first_product_term_drives_low: assert property (
        @(posedge clk)
        ((~A1) & (~A2) & (~B1) & B2) |-> (X == 1'b0)
    );

    // The second product term forces X low.
    check_second_product_term_drives_low: assert property (
        @(posedge clk)
        (A1 & A2 & (~B1) & (~B2)) |-> (X == 1'b0)
    );

    // X can be low only for the two implemented minterms.
    check_low_output_only_in_implemented_cases: assert property (
        @(posedge clk)
        (X == 1'b0) |-> (((~A1) & (~A2) & (~B1) & B2) | (A1 & A2 & (~B1) & (~B2)))
    );

    // B1 high blocks both product terms and makes X high.
    check_b1_high_forces_high: assert property (
        @(posedge clk)
        (B1 == 1'b1) |-> (X == 1'b1)
    );

    // With B1 low and B2 high, X reduces to A1 OR A2.
    check_b1_low_b2_high_reduces_to_or: assert property (
        @(posedge clk)
        ((~B1) & B2) |-> (X == (A1 | A2))
    );

    // With B1 low and B2 low, X reduces to NOT(A1 AND A2).
    check_b1_low_b2_low_reduces_to_nand: assert property (
        @(posedge clk)
        ((~B1) & (~B2)) |-> (X == ~(A1 & A2))
    );

endmodule