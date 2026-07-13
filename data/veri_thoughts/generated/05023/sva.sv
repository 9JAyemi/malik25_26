module sky130_fd_sc_ls__o41ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);

    // Combinational DUT; clk is an external sampling clock and no reset exists.

    // Y must match the implemented OAI/NAND logic.
    check_boolean_function: assert property (
        @(posedge clk) Y == ~(B1 & (A1 | A2 | A3 | A4))
    );

    // A low B1 input forces the NAND output high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) (!B1) |-> (Y == 1'b1)
    );

    // When all A inputs are low, the OR term is low and Y stays high.
    check_all_a_low_forces_y_high: assert property (
        @(posedge clk) (!A1 && !A2 && !A3 && !A4) |-> (Y == 1'b1)
    );

    // A high B1 with any high A input forces Y low.
    check_b1_and_any_a_force_y_low: assert property (
        @(posedge clk) (B1 && (A1 || A2 || A3 || A4)) |-> (Y == 1'b0)
    );

    // A low Y requires B1 to be high.
    check_y_low_requires_b1_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> (B1 == 1'b1)
    );

    // A low Y requires at least one A input to be high.
    check_y_low_requires_any_a_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> (A1 || A2 || A3 || A4)
    );

endmodule