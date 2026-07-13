module top_module_sva (
    input logic [3:0] in,
    input logic [3:0] out,
    input logic [3:0] wire_bs_out
);

    // Barrel shifter output is the input rotated left by 1 bit.
    check_barrel_shift_rotate_left1: assert property (
        @($global_clock) wire_bs_out == {in[2:0], in[3]}
    );

    // Two's complement stage outputs bitwise inverse plus one.
    check_twos_complement_stage: assert property (
        @($global_clock) out == ((~wire_bs_out) + 4'b0001)
    );

    // Top-level output matches the two's complement of the rotated input.
    check_end_to_end_function: assert property (
        @($global_clock) out == ((~{in[2:0], in[3]}) + 4'b0001)
    );

    // Zero input remains zero through rotation and two's complement.
    check_zero_input_maps_to_zero: assert property (
        @($global_clock) (in == 4'b0000) |-> (out == 4'b0000)
    );

    // All-ones input rotates to all ones and two's complement becomes one.
    check_all_ones_input_maps_to_one: assert property (
        @($global_clock) (in == 4'b1111) |-> (out == 4'b0001)
    );

    // A single MSB rotates into the LSB before two's complement.
    check_msb_only_input_maps_to_all_ones: assert property (
        @($global_clock) (in == 4'b1000) |-> (out == 4'b1111)
    );

endmodule