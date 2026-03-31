module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CI,
    input logic [3:0] S,
    input logic CO
);

// Full 5-bit result matches 4-bit A + 4-bit B + CI.
    check_full_add: assert property (
        @(posedge clk) disable iff (1'b0)
        {CO, S} == ({1'b0, A} + {1'b0, B} + CI)
    );

// Sum bit 0 is the XOR of A[0], B[0], and CI.
    check_sum_bit0: assert property (
        @(posedge clk) disable iff (1'b0)
        S[0] == (A[0] ^ B[0] ^ CI)
    );

// Sum bit 1 uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) disable iff (1'b0)
        S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI)))
    );

// Sum bit 2 uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) disable iff (1'b0)
        S[2] == (A[2] ^ B[2] ^ (
            (A[1] & B[1]) |
            (B[1] & ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI))) |
            (A[1] & ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI)))
        ))
    );

// Sum bit 3 uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) disable iff (1'b0)
        S[3] == (A[3] ^ B[3] ^ (
            (A[2] & B[2]) |
            (B[2] & (
                (A[1] & B[1]) |
                (B[1] & ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI))) |
                (A[1] & ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI)))
            )) |
            (A[2] & (
                (A[1] & B[1]) |
                (B[1] & ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI))) |
                (A[1] & ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI)))
            ))
        ))
    );

// Carry-out is the carry generated from bit 3.
    check_carry_out: assert property (
        @(posedge clk) disable iff (1'b0)
        CO == (
            (A[3] & B[3]) |
            (B[3] & (
                (A[2] & B[2]) |
                (B[2] & (
                    (A[1] & B[1]) |
                    (B[1] & ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI))) |
                    (A[1] & ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI)))
                )) |
                (A[2] & (
                    (A[1] & B[1]) |
                    (B[1] & ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI))) |
                    (A[1] & ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI)))
                ))
            )) |
            (A[3] & (
                (A[2] & B[2]) |
                (B[2] & (
                    (A[1] & B[1]) |
                    (B[1] & ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI))) |
                    (A[1] & ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI)))
                )) |
                (A[2] & (
                    (A[1] & B[1]) |
                    (B[1] & ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI))) |
                    (A[1] & ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI)))
                ))
            ))
        )
    );

endmodule
