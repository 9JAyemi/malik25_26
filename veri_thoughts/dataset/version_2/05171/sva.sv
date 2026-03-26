module binary_to_gray_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] G
);

    // G[0] directly matches A[0].
    check_gray_bit0: assert property (
        @(posedge clk) G[0] == A[0]
    );

    // G[1] is the XOR of A[0] and A[1].
    check_gray_bit1: assert property (
        @(posedge clk) G[1] == (A[0] ^ A[1])
    );

    // G[2] is the XOR of A[1] and A[2].
    check_gray_bit2: assert property (
        @(posedge clk) G[2] == (A[1] ^ A[2])
    );

    // G[3] is the XOR of A[2] and A[3].
    check_gray_bit3: assert property (
        @(posedge clk) G[3] == (A[2] ^ A[3])
    );

    // The full Gray output matches the defined bit mapping.
    check_gray_vector: assert property (
        @(posedge clk) G == {(A[2] ^ A[3]), (A[1] ^ A[2]), (A[0] ^ A[1]), A[0]}
    );

endmodule