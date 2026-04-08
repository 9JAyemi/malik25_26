module sky130_fd_sc_ls__inv_sva (
    input logic clk,
    input logic Y,
    input logic A
);

    // Y must always be the bitwise inversion of A.
    check_output_is_inverse: assert property (
        @(posedge clk) (Y === ~A)
    );

    // A low input drives Y high.
    check_low_input_drives_high_output: assert property (
        @(posedge clk) (A === 1'b0) |-> (Y === 1'b1)
    );

    // A high input drives Y low.
    check_high_input_drives_low_output: assert property (
        @(posedge clk) (A === 1'b1) |-> (Y === 1'b0)
    );

    // Unknown or high-impedance input produces an unknown output.
    check_unknown_input_produces_unknown_output: assert property (
        @(posedge clk) ((A === 1'bx) || (A === 1'bz)) |-> (Y === 1'bx)
    );

endmodule