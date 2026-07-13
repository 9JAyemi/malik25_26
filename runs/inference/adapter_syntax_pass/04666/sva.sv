module sky130_fd_sc_hvl__nand2_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Y
);

    // Y must equal the NAND of A and B.
    check_nand_function: assert property (
        @(posedge clk) Y == ~(A & B)
    );

    // Both high inputs must drive Y low.
    check_both_inputs_high_drive_low: assert property (
        @(posedge clk) (A && B) |-> !Y
    );

    // A low must drive Y high.
    check_a_low_drives_high: assert property (
        @(posedge clk) !A |-> Y
    );

    // B low must drive Y high.
    check_b_low_drives_high: assert property (
        @(posedge clk) !B |-> Y
    );

    // A low output can only occur when both inputs are high.
    check_low_output_requires_both_inputs_high: assert property (
        @(posedge clk) !Y |-> (A && B)
    );

endmodule