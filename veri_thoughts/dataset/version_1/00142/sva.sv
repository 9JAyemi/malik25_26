module sky130_fd_sc_ls__clkdlyinv5sd1_sva (
    input logic clk,
    input logic A,
    input logic Y
);

    // A low input drives a high output.
    check_input_low_drives_output_high: assert property (
        @(posedge clk) (A === 1'b0) |-> (Y === 1'b1)
    );

    // A high input drives a low output.
    check_input_high_drives_output_low: assert property (
        @(posedge clk) (A === 1'b1) |-> (Y === 1'b0)
    );

    // The sampled output matches the inversion of the sampled input.
    check_output_matches_inversion: assert property (
        @(posedge clk) ((A === 1'b0) || (A === 1'b1)) |-> (Y === ~A)
    );

endmodule