module sky130_fd_sc_hvl__o21a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);

    // X must equal (A1 OR A2) AND B1.
    check_o21a_function: assert property (
        @(posedge clk) X == ((A1 | A2) & B1)
    );

    // B1 low forces the output low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // With both OR inputs low, the output must be low.
    check_no_a_input_forces_x_low: assert property (
        @(posedge clk) (!A1 && !A2) |-> !X
    );

    // A1 high with B1 high drives the output high.
    check_a1_and_b1_drive_x_high: assert property (
        @(posedge clk) (A1 && B1) |-> X
    );

    // A2 high with B1 high drives the output high.
    check_a2_and_b1_drive_x_high: assert property (
        @(posedge clk) (A2 && B1) |-> X
    );

    // A high output requires B1 to be high.
    check_x_high_requires_b1_high: assert property (
        @(posedge clk) X |-> B1
    );

    // A high output requires at least one A input high.
    check_x_high_requires_a1_or_a2: assert property (
        @(posedge clk) X |-> (A1 || A2)
    );

endmodule