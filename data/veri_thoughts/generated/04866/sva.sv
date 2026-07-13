module sky130_fd_sc_hdll__or4_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Output matches the 4-input OR function.
    check_or_function: assert property (
        @(posedge clk) X == (A | B | C | D)
    );

    // A high forces the output high.
    check_a_drives_x_high: assert property (
        @(posedge clk) A |-> X
    );

    // B high forces the output high.
    check_b_drives_x_high: assert property (
        @(posedge clk) B |-> X
    );

    // C high forces the output high.
    check_c_drives_x_high: assert property (
        @(posedge clk) C |-> X
    );

    // D high forces the output high.
    check_d_drives_x_high: assert property (
        @(posedge clk) D |-> X
    );

    // All inputs low force the output low.
    check_all_inputs_low_drives_x_low: assert property (
        @(posedge clk) !(A | B | C | D) |-> !X
    );

    // Unchanged inputs keep the output unchanged.
    check_stable_inputs_keep_x_stable: assert property (
        @(posedge clk) $stable({A, B, C, D}) |-> $stable(X)
    );

endmodule