module sky130_fd_sc_hd__nand3_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    ///// NAND behavior /////

    // Y matches the 3-input NAND of A, B, and C.
    check_nand_function: assert property (
        @(posedge clk) Y == ~(A & B & C)
    );

    // All three HIGH inputs force Y LOW.
    check_all_high_drives_low: assert property (
        @(posedge clk) (A && B && C) |-> !Y
    );

    // A LOW forces Y HIGH.
    check_a_low_drives_high: assert property (
        @(posedge clk) !A |-> Y
    );

    // B LOW forces Y HIGH.
    check_b_low_drives_high: assert property (
        @(posedge clk) !B |-> Y
    );

    // C LOW forces Y HIGH.
    check_c_low_drives_high: assert property (
        @(posedge clk) !C |-> Y
    );

    // A LOW output requires all three inputs HIGH.
    check_low_output_requires_all_high: assert property (
        @(posedge clk) !Y |-> (A && B && C)
    );

endmodule