module bin_to_gray_sva (
    input logic [3:0] bin,
    input logic [3:0] gray
);

    // gray[3] passes through bin[3].
    check_gray_bit3_passthrough: assert property (
        @($global_clock) gray[3] == bin[3]
    );

    // gray[2] is bin[3] XOR bin[2].
    check_gray_bit2_xor: assert property (
        @($global_clock) gray[2] == (bin[3] ^ bin[2])
    );

    // gray[1] is bin[2] XOR bin[1].
    check_gray_bit1_xor: assert property (
        @($global_clock) gray[1] == (bin[2] ^ bin[1])
    );

    // gray[0] is bin[1] XOR bin[0].
    check_gray_bit0_xor: assert property (
        @($global_clock) gray[0] == (bin[1] ^ bin[0])
    );

    // The full Gray vector matches the implemented encoding.
    check_full_gray_encoding: assert property (
        @($global_clock) gray == {bin[3], (bin[3] ^ bin[2]), (bin[2] ^ bin[1]), (bin[1] ^ bin[0])}
    );

    // If bin is unchanged, gray is unchanged.
    check_stable_bin_implies_stable_gray: assert property (
        @($global_clock) $stable(bin) |-> $stable(gray)
    );

    // A change only on bin[0] affects only gray[0].
    check_bin0_change_effect: assert property (
        @($global_clock) ($stable(bin[3:1]) && $changed(bin[0])) |-> ($stable(gray[3:1]) && $changed(gray[0]))
    );

    // A change only on bin[1] affects gray[1:0] and not gray[3:2].
    check_bin1_change_effect: assert property (
        @($global_clock) ($stable({bin[3:2], bin[0]}) && $changed(bin[1])) |-> ($stable(gray[3:2]) && $changed(gray[1]) && $changed(gray[0]))
    );

    // A change only on bin[2] affects gray[2:1] and not gray[3] or gray[0].
    check_bin2_change_effect: assert property (
        @($global_clock) ($stable({bin[3], bin[1:0]}) && $changed(bin[2])) |-> ($stable(gray[3]) && $changed(gray[2]) && $changed(gray[1]) && $stable(gray[0]))
    );

    // A change only on bin[3] affects gray[3:2] and not gray[1:0].
    check_bin3_change_effect: assert property (
        @($global_clock) ($stable(bin[2:0]) && $changed(bin[3])) |-> ($changed(gray[3]) && $changed(gray[2]) && $stable(gray[1:0]))
    );

endmodule