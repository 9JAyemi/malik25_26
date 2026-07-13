module bin2gray_sva (
    input logic [3:0] binary,
    input logic [3:0] gray
);
    // gray[3] equals binary[3].
    check_gray_bit3_passthrough: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        (gray[3] == binary[3])
    );

    // gray[2] equals binary[3] ^ binary[2].
    check_gray_bit2_xor: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        (gray[2] == (binary[3] ^ binary[2]))
    );

    // gray[1] equals binary[2] ^ binary[1].
    check_gray_bit1_xor: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        (gray[1] == (binary[2] ^ binary[1]))
    );

    // gray[0] equals binary[1] ^ binary[0].
    check_gray_bit0_xor: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        (gray[0] == (binary[1] ^ binary[0]))
    );

    // gray vector equals {binary[3], binary[3]^binary[2], binary[2]^binary[1], binary[1]^binary[0]}.
    check_gray_vector_mapping: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        (gray == {binary[3], (binary[3] ^ binary[2]), (binary[2] ^ binary[1]), (binary[1] ^ binary[0])})
    );

    // If binary is stable, gray must be stable (pure combinational mapping).
    check_gray_stable_when_binary_stable: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        $stable(binary) |-> $stable(gray)
    );

    // If only binary[0] changes, only gray[0] changes.
    check_gray_change_mask_bit0: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        ($changed(binary[0]) && $stable(binary[1:0])) |-> ($changed(gray[0]) && $stable(gray[3:1]))
    );

    // If only binary[1] changes, only gray[1] and gray[0] change.
    check_gray_change_mask_bit1: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        ($changed(binary[1]) && $stable(binary[2:0])) |-> ($changed(gray[1]) && $changed(gray[0]) && $stable(gray[3]))
    );

    // If only binary[2] changes, only gray[2], gray[1], and gray[0] change.
    check_gray_change_mask_bit2: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        ($changed(binary[2]) && $stable(binary[3:0])) |-> ($changed(gray[2]) && $changed(gray[1]) && $changed(gray[0]) && $stable(gray[3]))
    );

    // If only binary[3] changes, only gray[3] and gray[2] change.
    check_gray_change_mask_bit3: assert property (
        @(posedge binary[0] or negedge binary[0] or
          posedge binary[1] or negedge binary[1] or
          posedge binary[2] or negedge binary[2] or
          posedge binary[3] or negedge binary[3])
        ($changed(binary[3]) && $stable(binary[2:0])) |-> ($changed(gray[3]) && $changed(gray[2]) && $stable(gray[1:0]))
    );
endmodule