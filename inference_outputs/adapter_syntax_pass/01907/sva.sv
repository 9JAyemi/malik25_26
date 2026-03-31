module and_module_sva (
    input logic [7:0] i_bus1,
    input logic [7:0] i_bus2,
    input logic [7:0] o_bus
);

    // o_bus must equal the bitwise AND of i_bus1 and i_bus2.
    check_and_function: assert property (
        @($global_clock) o_bus == (i_bus1 & i_bus2)
    );

    // o_bus can only have bits set where both inputs have bits set.
    check_output_subset_of_inputs: assert property (
        @($global_clock) (o_bus & ~i_bus1) == 8'h00 && (o_bus & ~i_bus2) == 8'h00
    );

    // A high bit on i_bus1 must appear on o_bus.
    check_i_bus1_high_bits_appear_on_o_bus: assert property (
        @($global_clock) (i_bus1 & ~o_bus) == 8'h00
    );

    // A high bit on i_bus2 must appear on o_bus.
    check_i_bus2_high_bits_appear_on_o_bus: assert property (
        @($global_clock) (i_bus2 & ~o_bus) == 8'h00
    );

    // o_bus can only be high where both inputs are high.
    check_o_bus_high_only_where_inputs_high: assert property (
        @($global_clock) (o_bus & ~i_bus1 & ~i_bus2) == 8'h00
    );

    // o_bus must not assert bits where either input is low.
    check_o_bus_low_where_inputs_low: assert property (
        @($global_clock) (o_bus & ~(i_bus1 | i_bus2)) == 8'h00
    );

    // If both inputs are all ones, o_bus must be all ones.
    check_all_ones_case: assert property (
        @($global_clock) (i_bus1 == 8'hFF && i_bus2 == 8'hFF) |-> (o_bus == 8'hFF)
    );

    // If either input is all zeros, o_bus must be all zeros.
    check_zero_input_case: assert property (
        @($global_clock) ((i_bus1 == 8'h00) || (i_bus2 == 8'h00)) |-> (o_bus == 8'h00)
    );

endmodule