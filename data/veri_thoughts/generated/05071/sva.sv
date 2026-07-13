module complement_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B
);

    // No reset in RTL; assertions are sampled on clk.

    // B matches the bitwise complement of A.
    check_vector_complement: assert property (
        @(posedge clk) B === ~A
    );

    // B[0] is the complement of A[0].
    check_bit0_complement: assert property (
        @(posedge clk) B[0] === ~A[0]
    );

    // B[1] is the complement of A[1].
    check_bit1_complement: assert property (
        @(posedge clk) B[1] === ~A[1]
    );

    // B[2] is the complement of A[2].
    check_bit2_complement: assert property (
        @(posedge clk) B[2] === ~A[2]
    );

    // B[3] is the complement of A[3].
    check_bit3_complement: assert property (
        @(posedge clk) B[3] === ~A[3]
    );

endmodule