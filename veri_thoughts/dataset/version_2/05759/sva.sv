module digital_circuit_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic VPWR,
    input logic VGND
);

    // X must match the implemented combinational equation.
    check_x_equation: assert property (
        @(posedge clk) X == (A1 & (A2 | B1) & (C1 ^ D1))
    );

    // A low A1 forces X low.
    check_x_low_when_a1_low: assert property (
        @(posedge clk) !A1 |-> (X == 1'b0)
    );

    // If both A2 and B1 are low, X must be low.
    check_x_low_when_a2_b1_low: assert property (
        @(posedge clk) !(A2 | B1) |-> (X == 1'b0)
    );

    // If C1 and D1 do not differ, X must be low.
    check_x_low_when_xor_low: assert property (
        @(posedge clk) !(C1 ^ D1) |-> (X == 1'b0)
    );

    // X must be high when all three product terms are high.
    check_x_high_when_all_terms_high: assert property (
        @(posedge clk) (A1 & (A2 | B1) & (C1 ^ D1)) |-> (X == 1'b1)
    );

    // A high X requires A1 to be high.
    check_x_implies_a1_high: assert property (
        @(posedge clk) X |-> (A1 == 1'b1)
    );

    // A high X requires at least one of A2 or B1 to be high.
    check_x_implies_or_term_high: assert property (
        @(posedge clk) X |-> ((A2 | B1) == 1'b1)
    );

    // A high X requires C1 and D1 to differ.
    check_x_implies_xor_term_high: assert property (
        @(posedge clk) X |-> ((C1 ^ D1) == 1'b1)
    );

    // VPWR is tied high in the RTL.
    check_vpwr_tied_high: assert property (
        @(posedge clk) VPWR == 1'b1
    );

    // VGND is tied low in the RTL.
    check_vgnd_tied_low: assert property (
        @(posedge clk) VGND == 1'b0
    );

endmodule