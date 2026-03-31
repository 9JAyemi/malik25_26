module sky130_fd_sc_hd__xor2_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic X
);

    // Output equals the XOR of the two inputs.
    check_x_matches_xor: assert property (
        @(posedge clk) X == (A ^ B)
    );

    // Equal inputs drive the output low.
    check_equal_inputs_drive_low: assert property (
        @(posedge clk) (A == B) |-> !X
    );

    // Different inputs drive the output high.
    check_different_inputs_drive_high: assert property (
        @(posedge clk) (A != B) |-> X
    );

    // 0 ^ 0 produces 0.
    check_00_to_0: assert property (
        @(posedge clk) (!A && !B) |-> !X
    );

    // 0 ^ 1 produces 1.
    check_01_to_1: assert property (
        @(posedge clk) (!A && B) |-> X
    );

    // 1 ^ 0 produces 1.
    check_10_to_1: assert property (
        @(posedge clk) (A && !B) |-> X
    );

    // 1 ^ 1 produces 0.
    check_11_to_0: assert property (
        @(posedge clk) (A && B) |-> !X
    );

endmodule