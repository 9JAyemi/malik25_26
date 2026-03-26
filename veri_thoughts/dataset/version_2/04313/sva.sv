module top_module_sva (
    input logic [7:0]  and_input,
    input logic [15:0] shifter_input,
    input logic        select,
    input logic [7:0]  functional_output
);

    // Output matches the top-level combinational definition.
    check_functional_output_definition: assert property (
        @($global_clock)
        functional_output == (and_input | ((select === 1'b1) ? shifter_input[15:8] : shifter_input[7:0]))
    );

    // A select value of 1 uses the upper shifter byte.
    check_select_one_uses_upper_byte: assert property (
        @($global_clock)
        (select === 1'b1) |-> (functional_output == (and_input | shifter_input[15:8]))
    );

    // Any non-1 select value uses the lower shifter byte.
    check_select_not_one_uses_lower_byte: assert property (
        @($global_clock)
        (select !== 1'b1) |-> (functional_output == (and_input | shifter_input[7:0]))
    );

    // Zero and_input passes the upper byte when select is 1.
    check_zero_and_input_upper_path: assert property (
        @($global_clock)
        ((select === 1'b1) && (and_input == 8'h00)) |-> (functional_output == shifter_input[15:8])
    );

    // Zero and_input passes the lower byte when select is not 1.
    check_zero_and_input_lower_path: assert property (
        @($global_clock)
        ((select !== 1'b1) && (and_input == 8'h00)) |-> (functional_output == shifter_input[7:0])
    );

    // A zero upper byte makes the output equal and_input on the upper path.
    check_zero_upper_byte_passes_and_input: assert property (
        @($global_clock)
        ((select === 1'b1) && (shifter_input[15:8] == 8'h00)) |-> (functional_output == and_input)
    );

    // A zero lower byte makes the output equal and_input on the lower path.
    check_zero_lower_byte_passes_and_input: assert property (
        @($global_clock)
        ((select !== 1'b1) && (shifter_input[7:0] == 8'h00)) |-> (functional_output == and_input)
    );

    // Equal shifter bytes make the output independent of select.
    check_equal_shifter_bytes_ignore_select: assert property (
        @($global_clock)
        (shifter_input[15:8] == shifter_input[7:0]) |-> (functional_output == (and_input | shifter_input[7:0]))
    );

endmodule

bind top_module top_module_sva top_module_sva_inst (
    .and_input(and_input),
    .shifter_input(shifter_input),
    .select(select),
    .functional_output(functional_output)
);