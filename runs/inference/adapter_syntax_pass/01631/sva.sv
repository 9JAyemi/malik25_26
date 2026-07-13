module sky130_fd_sc_hd__o2bb2a_sva (
    input logic clk,
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // X matches the implemented NAND/OR/AND function.
    check_output_function: assert property (
        @(posedge clk) X == ((~(A2_N & A1_N)) & (B2 | B1))
    );

    // Both A inputs high force X low.
    check_a_inputs_both_high_force_low: assert property (
        @(posedge clk) (A1_N & A2_N) |-> !X
    );

    // Both B inputs low force X low.
    check_b_inputs_both_low_force_low: assert property (
        @(posedge clk) (!B1 & !B2) |-> !X
    );

    // A low X requires at least one A input high and at least one B input high.
    check_low_output_requires_active_inputs: assert property (
        @(posedge clk) !X |-> (A1_N | A2_N) && (B1 | B2)
    );

    // A high X requires both A inputs low or both B inputs low.
    check_high_output_requires_inactive_inputs: assert property (
        @(posedge clk) X |-> (!A1_N & !A2_N) || (!B1 & !B2)
    );

    // A low X cannot occur when both A inputs are low.
    check_low_output_requires_a_inputs_active: assert property (
        @(posedge clk) !X |-> (A1_N | A2_N)
    );

    // A low X cannot occur when both B inputs are low.
    check_low_output_requires_b_inputs_active: assert property (
        @(posedge clk) !X |-> (B1 | B2)
    );

    // A high X requires at least one A input high.
    check_high_output_requires_a_input_high: assert property (
        @(posedge clk) X |-> (A1_N | A2_N)
    );

    // A high X requires at least one B input high.
    check_high_output_requires_b_input_high: assert property (
        @(posedge clk) X |-> (B1 | B2)
    );

endmodule