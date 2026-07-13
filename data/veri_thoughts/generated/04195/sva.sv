module digital_circuit_sva (
    input logic clk,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Y
);

    // Sample the combinational RTL on an external formal clock.
    // Y must match the implemented OR-of-ANDs equation.
    check_output_equation: assert property (
        @(posedge clk) Y == ((A1_N & A2_N) | (B1 & B2))
    );

    // If the A1_N/A2_N term is high, Y must be high.
    check_a_term_drives_high: assert property (
        @(posedge clk) (A1_N & A2_N) |-> Y
    );

    // If the B1/B2 term is high, Y must be high.
    check_b_term_drives_high: assert property (
        @(posedge clk) (B1 & B2) |-> Y
    );

    // If neither product term is high, Y must be low.
    check_no_terms_means_low: assert property (
        @(posedge clk) (!(A1_N & A2_N) && !(B1 & B2)) |-> !Y
    );

    // A high Y must be caused by at least one product term.
    check_y_high_has_cause: assert property (
        @(posedge clk) Y |-> ((A1_N & A2_N) || (B1 & B2))
    );

endmodule