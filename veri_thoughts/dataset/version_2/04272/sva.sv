module adder4bit_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Ci,
    input logic [3:0] S,
    input logic       Co
);

    function automatic logic fa_co (
        input logic a,
        input logic b,
        input logic ci
    );
        fa_co = (a & b) | ((a ^ b) & ci);
    endfunction

    // Bit 0 sum matches the least-significant full adder.
    check_bit0_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Ci)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ fa_co(A[0], B[0], Ci))
    );

    // Bit 2 sum uses the ripple carry from bit 1.
    check_bit2_sum: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ fa_co(A[1], B[1], fa_co(A[0], B[0], Ci)))
    );

    // Bit 3 sum uses the ripple carry from bit 2.
    check_bit3_sum: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ fa_co(A[2], B[2], fa_co(A[1], B[1], fa_co(A[0], B[0], Ci))))
    );

    // Co is the inverted carry out of the most-significant full adder.
    check_inverted_carry_out: assert property (
        @(posedge clk) Co == ~fa_co(A[3], B[3], fa_co(A[2], B[2], fa_co(A[1], B[1], fa_co(A[0], B[0], Ci))))
    );

    // Outputs match a 4-bit add with inverted carry out.
    check_full_add_result: assert property (
        @(posedge clk) {~Co, S} == ({1'b0, A} + {1'b0, B} + {4'b0, Ci})
    );

endmodule