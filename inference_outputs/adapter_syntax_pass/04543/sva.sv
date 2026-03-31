module my_nand2b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B
);

    // Y matches the implemented NAND of A_N and B.
    check_y_matches_nand_function: assert property (
        @(posedge clk) Y == ~(~B & ~A_N)
    );

    // A high A_N forces Y high.
    check_a_n_high_forces_y_high: assert property (
        @(posedge clk) A_N |-> Y
    );

    // A low B forces Y high.
    check_b_low_forces_y_high: assert property (
        @(posedge clk) !B |-> Y
    );

    // A low A_N and high B force Y low.
    check_low_a_n_and_high_b_drive_y_low: assert property (
        @(posedge clk) (!A_N && B) |-> !Y
    );

    // A low Y requires both inputs to be low.
    check_y_low_requires_low_inputs: assert property (
        @(posedge clk) !Y |-> (!A_N && !B)
    );

endmodule