module four_bit_module_sva (
    input logic [3:0] input_data,
    input logic       output_data
);

    // Output is 1 when input_data equals 4'b1010.
    check_output_high_on_match: assert property (
        @($global_clock) (!$isunknown(input_data) && (input_data == 4'b1010)) |-> (output_data == 1'b1)
    );

    // Output is 0 when input_data does not equal 4'b1010.
    check_output_low_on_mismatch: assert property (
        @($global_clock) (!$isunknown(input_data) && (input_data != 4'b1010)) |-> (output_data == 1'b0)
    );

    // Output high implies input_data equals 4'b1010.
    check_high_implies_match: assert property (
        @($global_clock) (output_data == 1'b1) |-> (input_data == 4'b1010)
    );

    // Output matches comparator result exactly when input_data is known.
    check_functional_equivalence: assert property (
        @($global_clock) (!$isunknown(input_data)) |-> (output_data == (input_data == 4'b1010))
    );

endmodule