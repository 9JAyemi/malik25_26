module sky130_fd_sc_hd__o2bb2a_sva (
    input logic clk,
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // X matches the implemented NAND/OR/AND function.
    check_x_matches_function: assert property (
        @(posedge clk) X == ((~(A2_N & A1_N)) & (B2 | B1))
    );

    // Both A inputs high force X low.
    check_a_inputs_high_force_x_low: assert property (
        @(posedge clk) (A1_N & A2_N) |-> !X
    );

    // Both B inputs low force X low.
    check_b_inputs_low_force_x_low: assert property (
        @(posedge clk) (!B1 & !B2) |-> !X
    );

    // With A inputs low and either B input high, X is high.
    check_active_condition_drives_x_high: assert property (
        @(posedge clk) ((!A1_N & !A2_N) & (B1 | B2)) |-> X
    );

    // A high X requires at least one A input low and at least one B input high.
    check_x_high_requires_active_condition: assert property (
        @(posedge clk) X |-> ((!A1_N & !A2_N) & (B1 | B2))
    );

    // X can only be high when both A inputs are not both high.
    check_x_high_requires_a_not_both_high: assert property (
        @(posedge clk) X |-> !(A1_N & A2_N)
    );

    // X can only be high when at least one B input is high.
    check_x_high_requires_b_or: assert property (
        @(posedge clk) X |-> (B1 | B2)
    );

endmodule