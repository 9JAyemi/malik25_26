module sky130_fd_sc_hvl__nand2_sva (
    input logic Y,
    input logic A,
    input logic B
);

    // Y implements a 2-input NAND of A and B.
    check_nand_function: assert property (
        @($global_clock) Y === ~(A & B)
    );

    // Both high inputs force Y low.
    check_both_high_drive_low: assert property (
        @($global_clock) ((A === 1'b1) && (B === 1'b1)) |-> (Y === 1'b0)
    );

    // A low forces Y high.
    check_a_low_drives_high: assert property (
        @($global_clock) (A === 1'b0) |-> (Y === 1'b1)
    );

    // B low forces Y high.
    check_b_low_drives_high: assert property (
        @($global_clock) (B === 1'b0) |-> (Y === 1'b1)
    );

    // A low output requires both inputs high.
    check_low_output_requires_both_high: assert property (
        @($global_clock) (Y === 1'b0) |-> ((A === 1'b1) && (B === 1'b1))
    );

endmodule