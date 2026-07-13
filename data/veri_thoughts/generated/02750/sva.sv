module decoder_3to8_sva (
    input logic CLK,       // Checker clock (DUT has no clock/reset; pure combinational)
    input logic A,
    input logic B,
    input logic C,
    input logic [7:0] Y
);

    // Y[0] must equal ~A & ~B & ~C.
    check_y0_decode: assert property (
        @(posedge CLK) Y[0] == ((~A) & (~B) & (~C))
    );

    // Y[1] must equal ~A & ~B & C.
    check_y1_decode: assert property (
        @(posedge CLK) Y[1] == ((~A) & (~B) & ( C))
    );

    // Y[2] must equal ~A & B & ~C.
    check_y2_decode: assert property (
        @(posedge CLK) Y[2] == ((~A) & ( B) & (~C))
    );

    // Y[3] must equal ~A & B & C.
    check_y3_decode: assert property (
        @(posedge CLK) Y[3] == ((~A) & ( B) & ( C))
    );

    // Y[4] must equal A & ~B & ~C.
    check_y4_decode: assert property (
        @(posedge CLK) Y[4] == (( A) & (~B) & (~C))
    );

    // Y[5] must equal A & ~B & C.
    check_y5_decode: assert property (
        @(posedge CLK) Y[5] == (( A) & (~B) & ( C))
    );

    // Y[6] must equal A & B & ~C.
    check_y6_decode: assert property (
        @(posedge CLK) Y[6] == (( A) & ( B) & (~C))
    );

    // Y[7] must equal A & B & C.
    check_y7_decode: assert property (
        @(posedge CLK) Y[7] == (( A) & ( B) & ( C))
    );

    // Exactly one output bit must be HIGH (one-hot).
    check_onehot_y: assert property (
        @(posedge CLK) $onehot(Y)
    );

    // Inputs can be reconstructed from outputs: A == OR of Y[7:4].
    check_reconstruct_a: assert property (
        @(posedge CLK) A == (Y[7] | Y[6] | Y[5] | Y[4])
    );

    // Inputs can be reconstructed from outputs: B == OR of Y[7],Y[6],Y[3],Y[2].
    check_reconstruct_b: assert property (
        @(posedge CLK) B == (Y[7] | Y[6] | Y[3] | Y[2])
    );

    // Inputs can be reconstructed from outputs: C == OR of Y[7],Y[5],Y[3],Y[1].
    check_reconstruct_c: assert property (
        @(posedge CLK) C == (Y[7] | Y[5] | Y[3] | Y[1])
    );

endmodule