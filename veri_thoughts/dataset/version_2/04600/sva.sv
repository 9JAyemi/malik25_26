module binary_converter_sva (
    input logic A,
    input logic X
);

    // Output X is always the logical inverse of input A.
    check_output_complements_input: assert property (
        @($global_clock) X == ~A
    );

endmodule