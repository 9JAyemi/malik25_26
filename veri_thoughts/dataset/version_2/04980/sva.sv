module twos_complement_sva (
    input logic [3:0] data_in,
    input logic       reset,
    input logic [3:0] data_out
);

    // Reset forces the output to zero.
    check_reset_forces_zero: assert property (
        @($global_clock) reset |-> (data_out == 4'b0000)
    );

    // Outside reset, output is the 4-bit two's complement of input.
    check_twos_complement_value: assert property (
        @($global_clock) disable iff (reset)
        (data_out == ((~data_in) + 4'd1))
    );

    // Zero remains zero after two's complement.
    check_zero_maps_to_zero: assert property (
        @($global_clock) disable iff (reset)
        (data_in == 4'b0000) |-> (data_out == 4'b0000)
    );

    // 4'b1000 is self-negating in 4-bit two's complement.
    check_msb_only_maps_to_self: assert property (
        @($global_clock) disable iff (reset)
        (data_in == 4'b1000) |-> (data_out == 4'b1000)
    );

    // Negating the output returns the original input.
    check_inverse_relation: assert property (
        @($global_clock) disable iff (reset)
        (((~data_out) + 4'd1) == data_in)
    );

    // With stable input and reset low, output stays stable.
    check_stable_input_holds_output: assert property (
        @($global_clock) disable iff (reset)
        ($stable(data_in) && $stable(reset)) |-> $stable(data_out)
    );

    // Input value 1 maps to 4'b1111.
    check_one_maps_to_minus_one: assert property (
        @($global_clock) disable iff (reset)
        (data_in == 4'b0001) |-> (data_out == 4'b1111)
    );

    // Input value 4'b1111 maps to 1.
    check_minus_one_maps_to_one: assert property (
        @($global_clock) disable iff (reset)
        (data_in == 4'b1111) |-> (data_out == 4'b0001)
    );

endmodule