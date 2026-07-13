module binary_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       CIN,
    input logic [3:0] SUM,
    input logic       COUT
);

    // SUM[0] is the XOR of A[0], B[0], and CIN.
    check_sum_bit0_xor: assert property (
        @($global_clock) SUM[0] == (A[0] ^ B[0] ^ CIN)
    );

    // SUM[1] is the XOR of A[1], B[1], and the carry from bit 0.
    check_sum_bit1_xor: assert property (
        @($global_clock)
        SUM[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN)))
    );

    // SUM[2] is the XOR of A[2], B[2], and the carry from bit 1.
    check_sum_bit2_xor: assert property (
        @($global_clock)
        SUM[2] == (A[2] ^ B[2] ^
                   ((A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN)))))
    );

    // SUM[3] is the XOR of A[3], B[3], and the carry from bit 2.
    check_sum_bit3_xor: assert property (
        @($global_clock)
        SUM[3] == (A[3] ^ B[3] ^
                   ((A[2] & B[2]) |
                    (A[2] & ((A[1] & B[1]) |
                             (A[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))) |
                             (B[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))))) |
                    (B[2] & ((A[1] & B[1]) |
                             (A[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN))) |
                             (B[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN)))))))
    );

    // COUT is the carry out from the final full adder.
    check_cout_from_bit3: assert property (
        @($global_clock)
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
                                   (B[1] & ((A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN)))))))))
    );

    // The 5-bit result matches the arithmetic sum of A, B, and CIN.
    check_total_sum: assert property (
        @($global_clock) {COUT, SUM} == ({1'b0, A} + {1'b0, B} + {4'b0000, CIN})
    );

endmodule