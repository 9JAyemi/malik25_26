module sky130_fd_sc_hdll__inv_sva (
    input logic Y,
    input logic A,
    input logic clk
);

    // Output must always be the logical inversion of the input.
    check_inverter_function: assert property (
        @(posedge clk) Y === ~A
    );

endmodule