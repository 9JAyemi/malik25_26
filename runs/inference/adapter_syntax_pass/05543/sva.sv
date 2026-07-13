module sky130_fd_sc_ls__clkdlyinv3sd1_sva (
    input logic clk,
    input logic A,
    input logic Y
);

    // Y must always be the logical inverse of A.
    check_inversion_function: assert property (
        @(posedge clk) Y === ~A
    );

    // A low input must produce a high output.
    check_low_input_high_output: assert property (
        @(posedge clk) (A === 1'b0) |-> (Y === 1'b1)
    );

    // A high input must produce a low output.
    check_high_input_low_output: assert property (
        @(posedge clk) (A === 1'b1) |-> (Y === 1'b0)
    );

endmodule