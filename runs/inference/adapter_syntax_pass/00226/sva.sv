module desxor1_sva (
    input logic CLK,
    input logic [47:0] e,
    input logic [47:0] k,
    input logic [5:0] b1x,
    input logic [5:0] b2x,
    input logic [5:0] b3x,
    input logic [5:0] b4x,
    input logic [5:0] b5x,
    input logic [5:0] b6x,
    input logic [5:0] b7x,
    input logic [5:0] b8x
);
    // b1x equals e[5:0] XOR k[5:0].
    check_b1x_xor: assert property (
        @(posedge CLK) b1x == (e[5:0] ^ k[5:0])
    );
    // b2x equals e[11:6] XOR k[11:6].
    check_b2x_xor: assert property (
        @(posedge CLK) b2x == (e[11:6] ^ k[11:6])
    );
    // b3x equals e[17:12] XOR k[17:12].
    check_b3x_xor: assert property (
        @(posedge CLK) b3x == (e[17:12] ^ k[17:12])
    );
    // b4x equals e[23:18] XOR k[23:18].
    check_b4x_xor: assert property (
        @(posedge CLK) b4x == (e[23:18] ^ k[23:18])
    );
    // b5x equals e[29:24] XOR k[29:24].
    check_b5x_xor: assert property (
        @(posedge CLK) b5x == (e[29:24] ^ k[29:24])
    );
    // b6x equals e[35:30] XOR k[35:30].
    check_b6x_xor: assert property (
        @(posedge CLK) b6x == (e[35:30] ^ k[35:30])
    );
    // b7x equals e[41:36] XOR k[41:36].
    check_b7x_xor: assert property (
        @(posedge CLK) b7x == (e[41:36] ^ k[41:36])
    );
    // b8x equals e[47:42] XOR k[47:42].
    check_b8x_xor: assert property (
        @(posedge CLK) b8x == (e[47:42] ^ k[47:42])
    );
    // Concatenation of b1x..b8x equals e XOR k.
    check_concatenation: assert property (
        @(posedge CLK) {b8x, b7x, b6x, b5x, b4x, b3x, b2x, b1x} == (e ^ k)
    );
    // If e and k are stable, all outputs remain stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable(e) && $stable(k) |-> $stable({b8x, b7x, b6x, b5x, b4x, b3x, b2x, b1x})
    );
endmodule