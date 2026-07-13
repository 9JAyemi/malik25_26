module sky130_fd_sc_ms__or3_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C
);

    // X matches the OR of A, B, and C.
    check_or_function: assert property (
        @(posedge clk) X == (A | B | C)
    );

    // X is low when all inputs are low.
    check_all_inputs_low_drive_low: assert property (
        @(posedge clk) (!A && !B && !C) |-> !X
    );

    // A alone drives X high.
    check_a_only_drives_high: assert property (
        @(posedge clk) (A && !B && !C) |-> X
    );

    // B alone drives X high.
    check_b_only_drives_high: assert property (
        @(posedge clk) (!A && B && !C) |-> X
    );

    // C alone drives X high.
    check_c_only_drives_high: assert property (
        @(posedge clk) (!A && !B && C) |-> X
    );

    // A high X must be caused by at least one high input.
    check_output_high_has_high_input: assert property (
        @(posedge clk) X |-> (A || B || C)
    );

endmodule