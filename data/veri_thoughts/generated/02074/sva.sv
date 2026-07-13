module twos_complement_sva (
    input logic [3:0] in,
    input logic [3:0] out
);
    // No clock/reset in DUT; combinational. Use posedge of in[0] for sampling.
    logic [4:0] sum5;
    assign sum5 = {1'b0, in} + {1'b0, out};

    // out equals ~in + 1 (two's complement mapping).
    check_twos_complement_mapping: assert property (
        @(posedge in[0]) out == (~in + 4'd1)
    );

    // Inverse relationship holds: in equals ~out + 1.
    check_involution: assert property (
        @(posedge in[0]) in == (~out + 4'd1)
    );

    // Sum of in and out wraps to 0 on the low 4 bits.
    check_sum_low_nibble_zero: assert property (
        @(posedge in[0]) sum5[3:0] == 4'd0
    );

    // Carry-out of in + out equals OR reduction of in.
    check_sum_carry_vs_orin: assert property (
        @(posedge in[0]) sum5[4] == (|in)
    );

    // Zero maps to zero.
    check_zero_in_to_out: assert property (
        @(posedge in[0]) (in == 4'd0) |-> (out == 4'd0)
    );

    // Only zero maps to zero.
    check_zero_only_if_in_zero: assert property (
        @(posedge in[0]) (out == 4'd0) |-> (in == 4'd0)
    );

    // LSB is preserved by two's complement.
    check_lsb_preserved: assert property (
        @(posedge in[0]) out[0] == in[0]
    );

    // Value 8 maps to itself.
    check_eight_maps_to_eight: assert property (
        @(posedge in[0]) (in == 4'd8) |-> (out == 4'd8)
    );

    // Only value 8 maps to 8.
    check_only_eight_maps_to_eight: assert property (
        @(posedge in[0]) (out == 4'd8) |-> (in == 4'd8)
    );

    // Out is never exactly bitwise-not of in (addition of 1 ensures difference).
    check_not_pure_bitwise_not: assert property (
        @(posedge in[0]) out != ~in
    );
endmodule