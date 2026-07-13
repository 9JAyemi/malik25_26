module my_and_nor_assertions (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Y matches the implemented NOT/NOR/AND logic.
    check_output_function: assert property (
        @(posedge clk) Y == ~(~B1_N | (A1 & A2))
    );

    // A low B1_N forces the output low.
    check_b1n_low_forces_y_low: assert property (
        @(posedge clk) !B1_N |-> !Y
    );

    // When both A inputs are high, the output must be low.
    check_a1_a2_high_force_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

    // With B1_N high and A1 low, the output must be high.
    check_a1_low_allows_y_high: assert property (
        @(posedge clk) (B1_N && !A1) |-> Y
    );

    // With B1_N high and A2 low, the output must be high.
    check_a2_low_allows_y_high: assert property (
        @(posedge clk) (B1_N && !A2) |-> Y
    );

    // A high output requires B1_N to be high.
    check_y_high_requires_b1n_high: assert property (
        @(posedge clk) Y |-> B1_N
    );

    // A high output requires the A-input AND term to be low.
    check_y_high_requires_and_term_low: assert property (
        @(posedge clk) Y |-> !(A1 && A2)
    );

endmodule