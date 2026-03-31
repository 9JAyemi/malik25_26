module bin2gray_sva (
    input logic [3:0] bin,
    input logic [3:0] gray
);
    // gray[3] equals bin[3].
    check_gray3_maps_to_bin3: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        gray[3] == bin[3]
    );

    // gray[2] equals bin[3] ^ bin[2].
    check_gray2_maps_to_bin3_xor_bin2: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        gray[2] == (bin[3] ^ bin[2])
    );

    // gray[1] equals bin[2] ^ bin[1].
    check_gray1_maps_to_bin2_xor_bin1: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        gray[1] == (bin[2] ^ bin[1])
    );

    // gray[0] equals bin[1] ^ bin[0].
    check_gray0_maps_to_bin1_xor_bin0: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        gray[0] == (bin[1] ^ bin[0])
    );

    // gray vector equals {bin[3], bin[3]^bin[2], bin[2]^bin[1], bin[1]^bin[0]}.
    check_gray_vector_mapping: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        gray == {bin[3], (bin[3] ^ bin[2]), (bin[2] ^ bin[1]), (bin[1] ^ bin[0])}
    );

    // If bin[3] is stable, gray[3] is stable.
    check_gray3_stable_when_bin3_stable: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        $stable(bin[3]) |-> $stable(gray[3])
    );

    // If bin[2] is stable, gray[2] is stable.
    check_gray2_stable_when_bin2_stable: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        $stable(bin[2]) |-> $stable(gray[2])
    );

    // If bin[1] is stable, gray[1] is stable.
    check_gray1_stable_when_bin1_stable: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        $stable(bin[1]) |-> $stable(gray[1])
    );

    // If bin[0] is stable, gray[0] is stable.
    check_gray0_stable_when_bin0_stable: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        $stable(bin[0]) |-> $stable(gray[0])
    );

    // If bin[3] and bin[2] are stable, gray[2] is stable.
    check_gray2_stable_when_bin32_stable: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        ($stable(bin[3]) && $stable(bin[2])) |-> $stable(gray[2])
    );

    // If bin[2] and bin[1] are stable, gray[1] is stable.
    check_gray1_stable_when_bin21_stable: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        ($stable(bin[2]) && $stable(bin[1])) |-> $stable(gray[1])
    );

    // If bin[1] and bin[0] are stable, gray[0] is stable.
    check_gray0_stable_when_bin10_stable: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        ($stable(bin[1]) && $stable(bin[0])) |-> $stable(gray[0])
    );

    // If bin[3] and bin[1] are stable, gray[2] is stable.
    check_gray2_stable_when_bin31_stable: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        ($stable(bin[3]) && $stable(bin[1])) |-> $stable(gray[2])
    );

    // If bin[3] and bin[0] are stable, gray[1] is stable.
    check_gray1_stable_when_bin30_stable: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        ($stable(bin[3]) && $stable(bin[0])) |-> $stable(gray[1])
    );

    // If bin[2] and bin[0] are stable, gray[0] is stable.
    check_gray0_stable_when_bin20_stable: assert property (
        @(posedge bin[0] or negedge bin[0] or posedge bin[1] or negedge bin[1] or posedge bin[2] or negedge bin[2] or posedge bin[3] or negedge bin[3])
        ($stable(bin[2]) && $stable(bin[0])) |-> $stable(gray[0])
    );
endmodule