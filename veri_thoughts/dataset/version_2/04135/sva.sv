module sky130_fd_sc_lp__nand3b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B,
    input logic C
);

    // Combinational DUT sampled on an external clock; RTL has no reset.

    // Y matches the implemented NAND-with-inverted-A function.
    check_nand3b_boolean_function: assert property (
        @(posedge clk) Y == ~(B & ~A_N & C)
    );

    // Y can be LOW only for the single active minterm.
    check_output_low_only_on_active_minterm: assert property (
        @(posedge clk) !Y |-> (!A_N && B && C)
    );

    // The active minterm drives Y LOW.
    check_active_minterm_drives_low: assert property (
        @(posedge clk) (!A_N && B && C) |-> !Y
    );

    // A_N HIGH forces Y HIGH through the inverted A input.
    check_a_n_high_forces_y_high: assert property (
        @(posedge clk) A_N |-> Y
    );

    // B LOW forces Y HIGH.
    check_b_low_forces_y_high: assert property (
        @(posedge clk) !B |-> Y
    );

    // C LOW forces Y HIGH.
    check_c_low_forces_y_high: assert property (
        @(posedge clk) !C |-> Y
    );

endmodule