module top_module_assertions (
    input logic [3:0] in,
    input logic [1:0] X,
    input logic Y,
    input logic [3:0] out,
    input logic [4:0] sum
);

    // Y follows the sign bit of in.
    check_y_matches_sign_bit: assert property (
        @($global_clock) (Y == in[3])
    );

    // Negative inputs drive out to the 4-bit two's complement of in.
    check_negative_out_is_twos_comp: assert property (
        @($global_clock) in[3] |-> (out == ((~in) + 4'b0001))
    );

    // Non-negative inputs drive out to the zero-extended encoded X value.
    check_nonnegative_out_is_zero_extended_x: assert property (
        @($global_clock) !in[3] |-> (out == {2'b00, X})
    );

    // Effective value 0001 encodes to X == 0.
    check_encode_eff_0001_to_x0: assert property (
        @($global_clock)
        (((in[3] ? ((~in) + 4'b0001) : in) == 4'b0001)) |-> (X == 2'd0)
    );

    // Effective value 0010 encodes to X == 1.
    check_encode_eff_0010_to_x1: assert property (
        @($global_clock)
        (((in[3] ? ((~in) + 4'b0001) : in) == 4'b0010)) |-> (X == 2'd1)
    );

    // Effective value 0100 encodes to X == 2.
    check_encode_eff_0100_to_x2: assert property (
        @($global_clock)
        (((in[3] ? ((~in) + 4'b0001) : in) == 4'b0100)) |-> (X == 2'd2)
    );

    // Effective value 1000 encodes to X == 3.
    check_encode_eff_1000_to_x3: assert property (
        @($global_clock)
        (((in[3] ? ((~in) + 4'b0001) : in) == 4'b1000)) |-> (X == 2'd3)
    );

    // Non-one-hot effective values fall into the default X == 3 case.
    check_encode_non_onehot_defaults_to_x3: assert property (
        @($global_clock)
        (((in[3] ? ((~in) + 4'b0001) : in) != 4'b0001) &&
         ((in[3] ? ((~in) + 4'b0001) : in) != 4'b0010) &&
         ((in[3] ? ((~in) + 4'b0001) : in) != 4'b0100) &&
         ((in[3] ? ((~in) + 4'b0001) : in) != 4'b1000)) |-> (X == 2'd3)
    );

    // sum is the zero-extended 4-bit result of out + X.
    check_sum_matches_out_plus_x: assert property (
        @($global_clock) (sum == {1'b0, (out + X)})
    );

    // The MSB of sum is always zero because the adder result is 4 bits wide.
    check_sum_msb_is_zero: assert property (
        @($global_clock) (sum[4] == 1'b0)
    );

endmodule