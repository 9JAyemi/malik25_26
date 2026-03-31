module my_nand2b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B
);

    // Y must match the implemented NAND of A_N and B.
    check_nand_function: assert property (
        @(posedge clk) Y == ~(~A_N & ~B)
    );

    // A low A_N forces the NAND output low.
    check_a_n_low_forces_y_low: assert property (
        @(posedge clk) !A_N |-> !Y
    );

    // A low B forces the NAND output low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) !B |-> !Y
    );

    // Both inputs high drive the NAND output high.
    check_both_inputs_high_drive_y_high: assert property (
        @(posedge clk) (A_N && B) |-> Y
    );

    // A high output requires both inputs high.
    check_y_high_requires_both_inputs_high: assert property (
        @(posedge clk) Y |-> (A_N && B)
    );

    // A low output means at least one input is low.
    check_y_low_requires_some_input_low: assert property (
        @(posedge clk) !Y |-> (!A_N || !B)
    );

endmodule