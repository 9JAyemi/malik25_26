module sky130_fd_sc_hd__o21bai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Y matches the implemented NAND of (~B1_N) and (A1 | A2).
    check_function_equivalence: assert property (
        @(posedge clk) Y == ~((~B1_N) & (A1 | A2))
    );

    // A low B1_N forces the NAND output low.
    check_b1n_low_forces_y_low: assert property (
        @(posedge clk) !B1_N |-> !Y
    );

    // With B1_N high, both A inputs low force the OR term low and Y high.
    check_a_inputs_low_force_y_high: assert property (
        @(posedge clk) (B1_N && !A1 && !A2) |-> Y
    );

    // With B1_N high, any high A input forces the OR term high and Y low.
    check_a_inputs_high_force_y_low: assert property (
        @(posedge clk) (B1_N && (A1 || A2)) |-> !Y
    );

    // A high Y requires B1_N high and the OR term low.
    check_y_high_requires_b1n_and_or_low: assert property (
        @(posedge clk) Y |-> (B1_N && !A1 && !A2)
    );

    // A low Y requires B1_N low or the OR term high.
    check_y_low_requires_b1n_low_or_or_high: assert property (
        @(posedge clk) !Y |-> (!B1_N || (A1 || A2))
    );

endmodule