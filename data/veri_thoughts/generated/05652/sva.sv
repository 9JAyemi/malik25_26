module sky130_fd_sc_lp__bufinv_sva (
    input logic Y,
    input logic A
);

    // Output is always the logical inversion of the input.
    check_output_inverts_input: assert property (
        @($global_clock) (Y === ~A)
    );

endmodule