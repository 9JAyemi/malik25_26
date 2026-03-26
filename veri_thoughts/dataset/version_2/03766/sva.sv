module inverter_sva (
    input logic signal,
    input logic inverted_signal
);

    // Output matches the bitwise inversion of the input.
    check_output_is_inverse: assert property (
        @($global_clock) inverted_signal === ~signal
    );

endmodule