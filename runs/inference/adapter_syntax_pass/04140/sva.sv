module odd_even_sva (
    input logic [2:0] input_bits,
    input logic [1:0] output_bits
);

    // Output is always one-hot.
    check_output_onehot: assert property (
        @($global_clock) $onehot(output_bits)
    );

    // Even input bits select 2'b10.
    check_even_input_encoding: assert property (
        @($global_clock) (input_bits[0] == 1'b0) |-> (output_bits == 2'b10)
    );

    // Odd input bits select 2'b01.
    check_odd_input_encoding: assert property (
        @($global_clock) (input_bits[0] == 1'b1) |-> (output_bits == 2'b01)
    );

endmodule