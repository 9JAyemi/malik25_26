module binary_to_gray_sva (
    input  logic        CLK,
    input  logic [3:0]  B,
    input  logic [3:0]  G
);
    // G[0] equals B[0].
    check_g0_map: assert property (
        @(posedge CLK) disable iff (1'b0) (G[0] == B[0])
    );

    // G[1] equals B[0] XOR B[1].
    check_g1_xor: assert property (
        @(posedge CLK) disable iff (1'b0) (G[1] == (B[0] ^ B[1]))
    );

    // G[2] equals B[1] XOR B[2].
    check_g2_xor: assert property (
        @(posedge CLK) disable iff (1'b0) (G[2] == (B[1] ^ B[2]))
    );

    // G[3] equals B[2] XOR B[3].
    check_g3_xor: assert property (
        @(posedge CLK) disable iff (1'b0) (G[3] == (B[2] ^ B[3]))
    );

    // Vector form: G equals B XOR (B << 1).
    check_vector_equivalence: assert property (
        @(posedge CLK) disable iff (1'b0) (G == (B ^ (B << 1)))
    );
endmodule