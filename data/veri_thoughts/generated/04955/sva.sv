module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] S,
    input logic COUT
);

    // The concatenated carry-out and sum equal the 5-bit addition result.
    check_full_add_result: assert property (
        @(posedge clk)
        {COUT, S} == ({1'b0, A} + {1'b0, B} + CIN)
    );

    // Sum bit 0 matches a full-adder XOR of A[0], B[0], and CIN.
    check_sum_bit0: assert property (
        @(posedge clk)
        S[0] == (A[0] ^ B[0] ^ CIN)
    );

    // Sum bit 1 matches a full-adder XOR using the bit-0 carry.
    check_sum_bit1: assert property (
        @(posedge clk)
        S[1] == (A[1] ^ B[1] ^
                 ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN)))
    );

    // Sum bit 2 matches a full-adder XOR using the bit-1 carry.
    check_sum_bit2: assert property (
        @(posedge clk)
        S[2] == (A[2] ^ B[2] ^
                 ((A[1] & B[1]) |
                  (A[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))) |
                  (B[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN)))))
    );

    // Sum bit 3 matches a full-adder XOR using the bit-2 carry.
    check_sum_bit3: assert property (
        @(posedge clk)
        S[3] == (A[3] ^ B[3] ^
                 ((A[2] & B[2]) |
                  (A[2] & ((A[1] & B[1]) |
                           (A[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))) |
                           (B[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))))) |
                  (B[2] & ((A[1] & B[1]) |
                           (A[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))) |
                           (B[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN)))))))
    );

    // COUT matches the ripple-carry carry generated from the MSB stage.
    check_cout_equation: assert property (
        @(posedge clk)
        COUT == ((A[3] & B[3]) |
                 (A[3] & ((A[2] & B[2]) |
                          (A[2] & ((A[1] & B[1]) |
                                   (A[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))) |
                                   (B[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))))) |
                          (B[2] & ((A[1] & B[1]) |
                                   (A[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))) |
                                   (B[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))))))) |
                 (B[3] & ((A[2] & B[2]) |
                          (A[2] & ((A[1] & B[1]) |
                                   (A[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))) |
                                   (B[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))))) |
                          (B[2] & ((A[1] & B[1]) |
                                   (A[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))) |
                                   (B[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))))))))
    );

endmodule