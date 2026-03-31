module ripple_carry_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       CIN,
    input logic [3:0] SUM,
    input logic       COUT
);

    // SUM[0] is the XOR of A[0], B[0], and CIN.
    check_sum0_xor: assert property (
        @($global_clock) SUM[0] == (A[0] ^ B[0] ^ CIN)
    );

    // SUM[1] is the XOR of A[1], B[1], and the carry from bit 0.
    check_sum1_xor_with_carry0: assert property (
        @($global_clock) SUM[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])))
    );

    // SUM[2] is the XOR of A[2], B[2], and the carry from bit 1.
    check_sum2_xor_with_carry1: assert property (
        @($global_clock) SUM[2] == (A[2] ^ B[2] ^ (
            (A[1] & B[1]) |
            (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) |
            (((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & (A[1] & B[1]))
        ))
    );

    // SUM[3] is the XOR of A[3], B[3], and the carry from bit 2.
    check_sum3_xor_with_carry2: assert property (
        @($global_clock) SUM[3] == (A[3] ^ B[3] ^ (
            (A[2] & B[2]) |
            (B[2] & (
                (A[1] & B[1]) |
                (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) |
                (((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & (A[1] & B[1]))
            )) |
            (((A[1] & B[1]) |
              (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) |
              (((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & (A[1] & B[1]))) &
             (A[2] & B[2]))
        ))
    );

    // COUT is the carry out from the final full adder.
    check_cout_from_bit3: assert property (
        @($global_clock) COUT == (
            (A[3] & B[3]) |
            (B[3] & (
                (A[2] & B[2]) |
                (B[2] & (
                    (A[1] & B[1]) |
                    (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) |
                    (((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & (A[1] & B[1]))
                )) |
                (((A[1] & B[1]) |
                  (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) |
                  (((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & (A[1] & B[1]))) &
                 (A[2] & B[2]))
            )) |
            (((A[2] & B[2]) |
              (B[2] & (
                  (A[1] & B[1]) |
                  (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) |
                  (((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & (A[1] & B[1]))
              )) |
              (((A[1] & B[1]) |
                (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) |
                (((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & (A[1] & B[1]))) &
               (A[2] & B[2])))
             & (A[3] & B[3]))
        )
    );

endmodule