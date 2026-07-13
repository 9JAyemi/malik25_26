module ripple_carry_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] SUM,
    input logic CARRY
);

    // Full output matches the zero-extended sum of A and B.
    check_full_addition: assert property (
        @($global_clock) {CARRY, SUM} == ({1'b0, A} + {1'b0, B})
    );

    // SUM[0] is the stage-1 sum of A[0] and B[0].
    check_sum_bit0: assert property (
        @($global_clock) SUM[0] == (A[0] ^ B[0])
    );

    // SUM[1] includes the carry from bit 0.
    check_sum_bit1: assert property (
        @($global_clock) SUM[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // SUM[2] includes the propagated carry from bits 0 and 1.
    check_sum_bit2: assert property (
        @($global_clock)
        SUM[2] == (A[2] ^ B[2] ^
                   ((A[1] & B[1]) |
                    ((A[1] ^ B[1]) & (A[0] & B[0]))))
    );

    // SUM[3] includes the propagated carry from bits 0 through 2.
    check_sum_bit3: assert property (
        @($global_clock)
        SUM[3] == (A[3] ^ B[3] ^
                   ((A[2] & B[2]) |
                    ((A[2] ^ B[2]) &
                     ((A[1] & B[1]) |
                      ((A[1] ^ B[1]) & (A[0] & B[0]))))))
    );

    // CARRY is the final carry-out of the 4-bit ripple chain.
    check_carry_out: assert property (
        @($global_clock)
        CARRY == ((A[3] & B[3]) |
                  ((A[3] ^ B[3]) &
                   ((A[2] & B[2]) |
                    ((A[2] ^ B[2]) &
                     ((A[1] & B[1]) |
                      ((A[1] ^ B[1]) & (A[0] & B[0])))))))
    );

endmodule