module data_converter_sva (
    input logic [15:0] data_in,
    input logic [3:0]  data_out
);

    // Output must match the RTL conversion function.
    check_exact_conversion: assert property (
        @($global_clock)
        data_out == ((data_in[3:0] != 4'b0000) ? 4'b1111 : data_in[15:12])
    );

    // Any nonzero low nibble forces the output to all ones.
    check_low_nibble_nonzero_forces_ones: assert property (
        @($global_clock)
        (data_in[3:0] != 4'b0000) |-> (data_out == 4'b1111)
    );

    // A zero low nibble makes the output equal the upper nibble.
    check_low_nibble_zero_passes_upper_nibble: assert property (
        @($global_clock)
        (data_in[3:0] == 4'b0000) |-> (data_out == data_in[15:12])
    );

    // Stable upper and lower nibbles must keep the output stable.
    check_output_stable_when_relevant_inputs_stable: assert property (
        @($global_clock) disable iff ($initstate)
        ((data_in[15:12] == $past(data_in[15:12])) &&
         (data_in[3:0]   == $past(data_in[3:0]))) |-> (data_out == $past(data_out))
    );

    // An output change must come from the upper or lower nibble changing.
    check_output_change_requires_relevant_input_change: assert property (
        @($global_clock) disable iff ($initstate)
        (data_out != $past(data_out)) |-> ((data_in[15:12] != $past(data_in[15:12])) ||
                                           (data_in[3:0]   != $past(data_in[3:0])))
    );

endmodule