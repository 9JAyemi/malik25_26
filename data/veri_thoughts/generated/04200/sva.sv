module sky130_fd_sc_ls__clkdlyinv5sd3_sva (
    input logic clk,
    input logic A,
    input logic Y
);

    // Output always matches the inverted input.
    check_inversion_function: assert property (
        @(posedge clk) (Y === ~A)
    );

    // A sampled low input produces a sampled high output.
    check_low_input_high_output: assert property (
        @(posedge clk) (A === 1'b0) |-> (Y === 1'b1)
    );

    // A sampled high input produces a sampled low output.
    check_high_input_low_output: assert property (
        @(posedge clk) (A === 1'b1) |-> (Y === 1'b0)
    );

    // An unknown or high-Z input produces an unknown output.
    check_unknown_input_unknown_output: assert property (
        @(posedge clk) ((A !== 1'b0) && (A !== 1'b1)) |-> (Y === 1'bx)
    );

endmodule