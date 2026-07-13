module sky130_fd_sc_hdll__o2bb2ai_sva (
    input logic clk,
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // Y matches the implemented NAND/OR/NAND/BUF function.
    check_y_function: assert property (
        @(posedge clk) Y == ~((~(A2_N & A1_N)) & (B2 | B1))
    );

    // All NAND inputs high force Y high.
    check_all_nand_inputs_high_drive_y_high: assert property (
        @(posedge clk) (A1_N & A2_N & ~B1 & ~B2) |-> Y
    );

    // Both B inputs low force Y high.
    check_b_inputs_low_drive_y_high: assert property (
        @(posedge clk) (~B1 & ~B2) |-> Y
    );

    // Both A inputs low force Y low.
    check_a_inputs_low_drive_y_low: assert property (
        @(posedge clk) (~A1_N & ~A2_N) |-> ~Y
    );

    // Both B inputs high force Y low.
    check_b_inputs_high_drive_y_low: assert property (
        @(posedge clk) (B1 & B2) |-> ~Y
    );

    // Both A inputs high force Y low.
    check_a_inputs_high_drive_y_low: assert property (
        @(posedge clk) (A1_N & A2_N) |-> ~Y
    );

    // A low Y requires both B inputs high and at least one A input low.
    check_y_low_requires_b_high_and_a_not_both_high: assert property (
        @(posedge clk) ~Y |-> (B1 & B2 & ~(A1_N & A2_N))
    );

    // A high Y requires at least one A input high and at least one B input low.
    check_y_high_requires_a_not_both_high_and_b_not_both_high: assert property (
        @(posedge clk) Y |-> ((A1_N | A2_N) & (~B1 | ~B2))
    );

endmodule