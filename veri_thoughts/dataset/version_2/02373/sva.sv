module twos_complement_sva (
    input  logic        clk,   // No clock/reset in DUT; use external clk for sampling
    input  logic [3:0]  in,
    input  logic [3:0]  out
);
    // out implements two's complement of in (4-bit wrap)
    check_twos_complement_equation: assert property (
        @(posedge clk) out == ((~in) + 4'd1)
    );

    // in + out wraps to zero modulo 16
    check_additive_inverse_mod16: assert property (
        @(posedge clk) (in + out) == 4'd0
    );

    // 0 maps to 0
    check_zero_maps_to_zero: assert property (
        @(posedge clk) (in == 4'd0) |-> (out == 4'd0)
    );

    // 1 maps to 0xF
    check_one_maps_to_all_ones: assert property (
        @(posedge clk) (in == 4'd1) |-> (out == 4'hF)
    );

    // 0xF maps to 1
    check_all_ones_maps_to_one: assert property (
        @(posedge clk) (in == 4'hF) |-> (out == 4'd1)
    );

    // Two's complement equals (0 - in) modulo 16
    check_subtraction_form: assert property (
        @(posedge clk) out == (4'd0 - in)
    );

    // Double two's complement returns original value
    check_double_complement_is_identity: assert property (
        @(posedge clk) ((~out) + 4'd1) == in
    );

    // Bitwise NOT of out equals (in - 1) modulo 16
    check_not_out_equals_in_minus_one: assert property (
        @(posedge clk) (~out) == (in - 4'd1)
    );

    // LSB is preserved by two's complement
    check_lsb_preserved: assert property (
        @(posedge clk) out[0] == in[0]
    );

    // Minimum 4-bit value (8) maps to itself
    check_min_int_maps_to_itself: assert property (
        @(posedge clk) (in == 4'd8) |-> (out == 4'd8)
    );
endmodule