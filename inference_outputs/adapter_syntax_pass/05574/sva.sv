module sky130_fd_sc_hdll__o2bb2ai_sva (
    input logic clk,
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // Y matches the implemented NAND/OR/NAND/BUF function.
    check_y_matches_function: assert property (
        @(posedge clk) Y == ~((~(A2_N & A1_N)) & (B2 | B1))
    );

    // Both A inputs high force Y high.
    check_a_inputs_high_drive_y_high: assert property (
        @(posedge clk) (A1_N & A2_N) |-> Y
    );

    // Both B inputs low force Y high.
    check_b_inputs_low_drive_y_high: assert property (
        @(posedge clk) (!B1 & !B2) |-> Y
    );

    // A1_N low with either B input high forces Y low.
    check_a1_low_with_b_high_drives_y_low: assert property (
        @(posedge clk) (!A1_N & (B1 | B2)) |-> !Y
    );

    // A2_N low with either B input high forces Y low.
    check_a2_low_with_b_high_drives_y_low: assert property (
        @(posedge clk) (!A2_N & (B1 | B2)) |-> !Y
    );

    // A1_N low with both B inputs low forces Y high.
    check_a1_low_with_b_low_drives_y_high: assert property (
        @(posedge clk) (!A1_N & !B1 & !B2) |-> Y
    );

    // A2_N low with both B inputs low forces Y high.
    check_a2_low_with_b_low_drives_y_high: assert property (
        @(posedge clk) (!A2_N & !B1 & !B2) |-> Y
    );

endmodule