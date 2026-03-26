module sky130_fd_sc_lp__o41a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);

    // X matches the implemented OR-then-AND function.
    check_functional_equivalence: assert property (
        @(posedge clk) X == (B1 & (A1 | A2 | A3 | A4))
    );

    // B1 low forces the output low.
    check_b1_gates_output_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // No asserted A input forces the output low.
    check_all_a_low_forces_x_low: assert property (
        @(posedge clk) !(A1 | A2 | A3 | A4) |-> !X
    );

    // A high output requires B1 to be high.
    check_x_high_requires_b1: assert property (
        @(posedge clk) X |-> B1
    );

    // A high output requires at least one A input high.
    check_x_high_requires_any_a: assert property (
        @(posedge clk) X |-> (A1 | A2 | A3 | A4)
    );

    // A1 can drive the output high when B1 is high.
    check_a1_path_to_x: assert property (
        @(posedge clk) (B1 & A1) |-> X
    );

    // A2 can drive the output high when B1 is high.
    check_a2_path_to_x: assert property (
        @(posedge clk) (B1 & A2) |-> X
    );

    // A3 can drive the output high when B1 is high.
    check_a3_path_to_x: assert property (
        @(posedge clk) (B1 & A3) |-> X
    );

    // A4 can drive the output high when B1 is high.
    check_a4_path_to_x: assert property (
        @(posedge clk) (B1 & A4) |-> X
    );

endmodule