module binary_to_gray_sva (
    input logic clk,
    input logic [3:0] BIN,
    input logic [3:0] GRAY
);

    // GRAY[0] is the XOR of BIN[0] and BIN[1].
    check_gray_bit0_xor: assert property (
        @(posedge clk) GRAY[0] == (BIN[0] ^ BIN[1])
    );

    // GRAY[1] is the XOR of BIN[1] and BIN[2].
    check_gray_bit1_xor: assert property (
        @(posedge clk) GRAY[1] == (BIN[1] ^ BIN[2])
    );

    // GRAY[2] is the XOR of BIN[2] and BIN[3].
    check_gray_bit2_xor: assert property (
        @(posedge clk) GRAY[2] == (BIN[2] ^ BIN[3])
    );

    // GRAY[3] directly copies BIN[3].
    check_gray_bit3_copy: assert property (
        @(posedge clk) GRAY[3] == BIN[3]
    );

    // The full GRAY vector matches the implemented mapping.
    check_gray_vector_map: assert property (
        @(posedge clk) GRAY == {BIN[3], (BIN[2] ^ BIN[3]), (BIN[1] ^ BIN[2]), (BIN[0] ^ BIN[1])}
    );

    // A stable BIN keeps the full GRAY output stable.
    check_stable_bin_keeps_gray_stable: assert property (
        @(posedge clk) !$initstate && $stable(BIN) |-> $stable(GRAY)
    );

    // GRAY[0] only depends on BIN[1:0].
    check_gray0_dependency: assert property (
        @(posedge clk) !$initstate && $stable(BIN[1:0]) |-> $stable(GRAY[0])
    );

    // GRAY[1] only depends on BIN[2:1].
    check_gray1_dependency: assert property (
        @(posedge clk) !$initstate && $stable(BIN[2:1]) |-> $stable(GRAY[1])
    );

    // GRAY[2] only depends on BIN[3:2].
    check_gray2_dependency: assert property (
        @(posedge clk) !$initstate && $stable(BIN[3:2]) |-> $stable(GRAY[2])
    );

    // GRAY[3] only depends on BIN[3].
    check_gray3_dependency: assert property (
        @(posedge clk) !$initstate && $stable(BIN[3]) |-> $stable(GRAY[3])
    );

endmodule