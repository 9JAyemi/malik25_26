module gray_code_converter_sva (
    input logic clk,
    input logic [3:0] binary,
    input logic [3:0] gray
);
    // gray[0] equals binary[0].
    check_map_g0_from_b0: assert property (
        @(posedge clk) gray[0] == binary[0]
    );

    // gray[1] equals binary[0] XOR binary[1].
    check_map_g1_from_b01: assert property (
        @(posedge clk) gray[1] == (binary[0] ^ binary[1])
    );

    // gray[2] equals binary[1] XOR binary[2].
    check_map_g2_from_b12: assert property (
        @(posedge clk) gray[2] == (binary[1] ^ binary[2])
    );

    // gray[3] equals binary[2] XOR binary[3].
    check_map_g3_from_b23: assert property (
        @(posedge clk) gray[3] == (binary[2] ^ binary[3])
    );

    // gray vector matches bitwise mapping from binary.
    check_map_vector: assert property (
        @(posedge clk) gray == { (binary[2] ^ binary[3]), (binary[1] ^ binary[2]), (binary[0] ^ binary[1]), binary[0] }
    );

    // If binary is stable, gray remains stable.
    check_stable_binary_implies_stable_gray: assert property (
        @(posedge clk) $stable(binary) |-> $stable(gray)
    );

    // gray[0] changes iff binary[0] changes.
    check_change_g0_iff_b0: assert property (
        @(posedge clk) $changed(gray[0]) == $changed(binary[0])
    );

    // gray[1] change equals parity of changes on binary[0] and binary[1].
    check_change_g1_parity: assert property (
        @(posedge clk) $changed(gray[1]) == ($changed(binary[0]) ^ $changed(binary[1]))
    );

    // gray[2] change equals parity of changes on binary[1] and binary[2].
    check_change_g2_parity: assert property (
        @(posedge clk) $changed(gray[2]) == ($changed(binary[1]) ^ $changed(binary[2]))
    );

    // gray[3] change equals parity of changes on binary[2] and binary[3].
    check_change_g3_parity: assert property (
        @(posedge clk) $changed(gray[3]) == ($changed(binary[2]) ^ $changed(binary[3]))
    );
endmodule