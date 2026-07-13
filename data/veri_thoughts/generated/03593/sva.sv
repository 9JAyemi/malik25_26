module sky130_fd_sc_ms__nand3_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);

    // Y matches the 3-input NAND of A, B, and C.
    check_nand_function: assert property (
        @(posedge clk) Y === ~(A & B & C)
    );

    // When all three inputs are high, Y must be low.
    check_all_high_drives_low: assert property (
        @(posedge clk) ((A === 1'b1) && (B === 1'b1) && (C === 1'b1)) |-> (Y === 1'b0)
    );

    // If any input is low, Y must be high.
    check_any_low_drives_high: assert property (
        @(posedge clk) ((A === 1'b0) || (B === 1'b0) || (C === 1'b0)) |-> (Y === 1'b1)
    );

    // A low Y can only occur when all inputs are high.
    check_low_output_requires_all_high: assert property (
        @(posedge clk) (Y === 1'b0) |-> ((A === 1'b1) && (B === 1'b1) && (C === 1'b1))
    );

    // A high Y requires at least one input to be low.
    check_high_output_requires_any_low: assert property (
        @(posedge clk) (Y === 1'b1) |-> ((A === 1'b0) || (B === 1'b0) || (C === 1'b0))
    );

endmodule