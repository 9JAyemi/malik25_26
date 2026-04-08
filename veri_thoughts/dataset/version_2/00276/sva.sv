module booth_encoder_7_new_sva (
    input logic        clk,
    input logic [2:0]  B_in,
    input logic [2:0]  A_out
);

    // A_out[0] is the OR of the two mixed-polarity low-bit terms.
    check_aout0_function: assert property (
        @(posedge clk)
        A_out[0] == ((B_in[0] & (~B_in[1])) | ((~B_in[0]) & B_in[1]))
    );

    // A_out[1] is the OR of (~B_in[0] & ~B_in[1]) and ~B_in[2].
    check_aout1_function: assert property (
        @(posedge clk)
        A_out[1] == (((~B_in[0]) & (~B_in[1])) | (~B_in[2]))
    );

    // A_out[2] is the OR of B_in[2] and (~B_in[0] & B_in[1]).
    check_aout2_function: assert property (
        @(posedge clk)
        A_out[2] == (B_in[2] | ((~B_in[0]) & B_in[1]))
    );

    // The full output vector matches the implemented combinational equations.
    check_aout_vector_function: assert property (
        @(posedge clk)
        A_out == {
            (B_in[2] | ((~B_in[0]) & B_in[1])),
            (((~B_in[0]) & (~B_in[1])) | (~B_in[2])),
            ((B_in[0] & (~B_in[1])) | ((~B_in[0]) & B_in[1]))
        }
    );

    // A low B_in[2] forces A_out[1] high through the direct OR term.
    check_b2_low_forces_aout1_high: assert property (
        @(posedge clk)
        (!B_in[2]) |-> A_out[1]
    );

    // A high B_in[2] forces A_out[2] high through the direct OR term.
    check_b2_high_forces_aout2_high: assert property (
        @(posedge clk)
        B_in[2] |-> A_out[2]
    );

    // Equal low-order input bits clear A_out[0].
    check_equal_low_bits_clear_aout0: assert property (
        @(posedge clk)
        (B_in[0] == B_in[1]) |-> (!A_out[0])
    );

    // B_in[0]=0 and B_in[1]=1 drives both the mixed term and A_out[2].
    check_01_low_bits_drive_outputs: assert property (
        @(posedge clk)
        ((!B_in[0]) && B_in[1]) |-> (A_out[0] && A_out[2])
    );

endmodule