module bin2gray_sva (
    input logic [3:0] bin,
    input logic [3:0] gray
);
    // No clock or reset in DUT; pure combinational. Use $global_clock for sampling.

    ///// Functional mapping checks /////
    // MSB mapping: gray[3] equals bin[3].
    check_gray3_equals_bin3: assert property (
        @(posedge $global_clock) (gray[3] == bin[3])
    );

    // gray[2] equals bin[3] XOR bin[2].
    check_gray2_equals_bin3_xor_bin2: assert property (
        @(posedge $global_clock) (gray[2] == (bin[3] ^ bin[2]))
    );

    // gray[1] equals bin[2] XOR bin[1].
    check_gray1_equals_bin2_xor_bin1: assert property (
        @(posedge $global_clock) (gray[1] == (bin[2] ^ bin[1]))
    );

    // gray[0] equals bin[1] XOR bin[0].
    check_gray0_equals_bin1_xor_bin0: assert property (
        @(posedge $global_clock) (gray[0] == (bin[1] ^ bin[0]))
    );

    // Vector mapping: gray equals bin XOR (bin shifted right by 1).
    check_gray_vector_equals_bin_xor_shift_right_1: assert property (
        @(posedge $global_clock) (gray == (bin ^ (bin >> 1)))
    );

    // Lower 3-bit vector mapping: gray[2:0] equals bin[3:1] XOR bin[2:0].
    check_gray_lower3_equals_bin31_xor_bin20: assert property (
        @(posedge $global_clock) (gray[2:0] == (bin[3:1] ^ bin[2:0]))
    );

endmodule