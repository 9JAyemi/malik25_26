module digital_circuit_sva (
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

    // Y must match the implemented OR-of-products equation.
    check_y_logic_equation: assert property (
        @(posedge clk) Y == ((A1 & A2) | (B1 & ~(A1 & A2)))
    );

    // When both A inputs are high, Y must be high.
    check_y_high_when_a1_a2_high: assert property (
        @(posedge clk) (A1 & A2) |-> Y
    );

    // When A1&A2 is low, Y must follow B1.
    check_y_follows_b1_when_a_term_low: assert property (
        @(posedge clk) ~(A1 & A2) |-> (Y == B1)
    );

    // A high B1 must drive Y high.
    check_y_high_when_b1_high: assert property (
        @(posedge clk) B1 |-> Y
    );

    // With B1 low and A1 low, Y must be low.
    check_y_low_when_b1_low_and_a1_low: assert property (
        @(posedge clk) (~B1 & ~A1) |-> ~Y
    );

    // With B1 low and A2 low, Y must be low.
    check_y_low_when_b1_low_and_a2_low: assert property (
        @(posedge clk) (~B1 & ~A2) |-> ~Y
    );

    // A low Y can only occur when B1 is low and A1&A2 is low.
    check_y_low_condition: assert property (
        @(posedge clk) ~Y |-> (~B1 & ~(A1 & A2))
    );

endmodule