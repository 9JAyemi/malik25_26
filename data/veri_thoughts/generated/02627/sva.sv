module bin_to_gray_sva (
    input logic CLK,
    input logic [3:0] bin,
    input logic [3:0] gray
);
    // Gray MSB equals binary MSB.
    check_gray_msb_copies_bin_msb: assert property (
        @(posedge CLK) gray[3] == bin[3]
    );

    // Gray[2] equals bin[3] XOR bin[2].
    check_gray_bit2_xor: assert property (
        @(posedge CLK) gray[2] == (bin[3] ^ bin[2])
    );

    // Gray[1] equals bin[2] XOR bin[1].
    check_gray_bit1_xor: assert property (
        @(posedge CLK) gray[1] == (bin[2] ^ bin[1])
    );

    // Gray[0] equals bin[1] XOR bin[0].
    check_gray_bit0_xor: assert property (
        @(posedge CLK) gray[0] == (bin[1] ^ bin[0])
    );

    // Toggling only bin[3] toggles gray[3] and gray[2]; lower bits hold.
    check_toggle_only_bin3_affects_gray3_and2: assert property (
        @(posedge CLK) ($changed(bin[3]) && $stable(bin[2:0]))
        |-> ($changed(gray[3]) && $changed(gray[2]) && $stable(gray[1:0]))
    );

    // Toggling only bin[2] toggles gray[2] and gray[1]; others hold.
    check_toggle_only_bin2_affects_gray2_and1: assert property (
        @(posedge CLK) ($changed(bin[2]) && $stable({bin[3], bin[1:0]}))
        |-> ($changed(gray[2]) && $changed(gray[1]) && $stable({gray[3], gray[0]}))
    );

    // Toggling only bin[1] toggles gray[1] and gray[0]; upper bits hold.
    check_toggle_only_bin1_affects_gray1_and0: assert property (
        @(posedge CLK) ($changed(bin[1]) && $stable({bin[3:2], bin[0]}))
        |-> ($changed(gray[1]) && $changed(gray[0]) && $stable(gray[3:2]))
    );

    // Toggling only bin[0] toggles only gray[0]; upper bits hold.
    check_toggle_only_bin0_affects_gray0_only: assert property (
        @(posedge CLK) ($changed(bin[0]) && $stable(bin[3:1]))
        |-> ($changed(gray[0]) && $stable(gray[3:1]))
    );

    // Binary bit2 reconstructs as gray[3] XOR gray[2].
    check_inverse_bin2_from_gray: assert property (
        @(posedge CLK) bin[2] == (gray[3] ^ gray[2])
    );

    // Binary bit0 reconstructs as gray[3]^gray[2]^gray[1]^gray[0].
    check_inverse_bin0_from_gray: assert property (
        @(posedge CLK) bin[0] == (gray[3] ^ gray[2] ^ gray[1] ^ gray[0])
    );
endmodule