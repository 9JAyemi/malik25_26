module binary_to_gray_sva (
    input logic clk,
    input logic [3:0] binary,
    input logic [3:0] gray
);
    ///// Bitwise mapping /////
    // MSB maps directly: gray[3] == binary[3].
    check_map_bit3: assert property (
        @(posedge clk) disable iff (1'b0) gray[3] == binary[3]
    );
    // gray[2] == binary[3] ^ binary[2].
    check_map_bit2: assert property (
        @(posedge clk) disable iff (1'b0) gray[2] == (binary[3] ^ binary[2])
    );
    // gray[1] == binary[2] ^ binary[1].
    check_map_bit1: assert property (
        @(posedge clk) disable iff (1'b0) gray[1] == (binary[2] ^ binary[1])
    );
    // gray[0] == binary[1] ^ binary[0].
    check_map_bit0: assert property (
        @(posedge clk) disable iff (1'b0) gray[0] == (binary[1] ^ binary[0])
    );

    ///// Vector mapping equivalence /////
    // gray == binary XOR (binary >> 1).
    check_map_vector: assert property (
        @(posedge clk) disable iff (1'b0) gray == (binary ^ {1'b0, binary[3:1]})
    );

    ///// Inverse relations derived from mapping /////
    // Recover binary[2] from gray: binary[2] == gray[2] ^ gray[3].
    check_inverse_b2: assert property (
        @(posedge clk) disable iff (1'b0) binary[2] == (gray[2] ^ gray[3])
    );
    // Recover binary[1] from gray: binary[1] == gray[1] ^ gray[2] ^ gray[3].
    check_inverse_b1: assert property (
        @(posedge clk) disable iff (1'b0) binary[1] == (gray[1] ^ gray[2] ^ gray[3])
    );
    // Recover binary[0] from gray: binary[0] == gray[0] ^ gray[1] ^ gray[2] ^ gray[3].
    check_inverse_b0: assert property (
        @(posedge clk) disable iff (1'b0) binary[0] == (gray[0] ^ gray[1] ^ gray[2] ^ gray[3])
    );

    ///// Additional consistency checks /////
    // Parity of gray equals LSB of binary.
    check_parity_relation: assert property (
        @(posedge clk) disable iff (1'b0) (^gray) == binary[0]
    );
    // Upper pair mapping consistency: {gray[3],gray[2]}.
    check_upper_pair_map: assert property (
        @(posedge clk) disable iff (1'b0) {gray[3], gray[2]} == {binary[3], (binary[3] ^ binary[2])}
    );
endmodule