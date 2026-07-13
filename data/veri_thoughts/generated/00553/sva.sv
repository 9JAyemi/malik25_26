module sky130_fd_sc_hd__clkinv_sva (
    input logic Y,
    input logic A
);

    // Output always equals the inversion of the input.
    check_output_is_inverted_input: assert property (
        @($global_clock) Y === ~A
    );

endmodule