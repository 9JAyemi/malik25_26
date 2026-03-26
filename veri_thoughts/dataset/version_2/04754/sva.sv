module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       C_in,
    input logic [3:0] S,
    input logic       C_out
);

    // No RTL clock or reset; sample combinational behavior on the global formal clock.

    // End-to-end output matches 4-bit addition with carry-in.
    check_full_sum: assert property (
        @($global_clock)
        {C_out, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, C_in})
    );

    // Stage 0 matches a 1-bit full-adder.
    check_stage0_add: assert property (
        @($global_clock)
        {((A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in)), S[0]} ==
        ({1'b0, A[0]} + {1'b0, B[0]} + {1'b0, C_in})
    );

    // Stage 1 matches a 1-bit full-adder fed by the bit 0 carry.
    check_stage1_add: assert property (
        @($global_clock)
        {((A[1] & B[1]) |
          (A[1] & ((A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in))) |
          (B[1] & ((A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in)))), S[1]} ==
        ({1'b0, A[1]} + {1'b0, B[1]} +
         {1'b0, ((A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in))})
    );

    // Stage 2 matches a 1-bit full-adder fed by the bit 1 carry.
    check_stage2_add: assert property (
        @($global_clock)
        {((A[2] & B[2]) |
          (A[2] & ((A[1] & B[1]) |
                   (A[1] & ((A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in))) |
                   (B[1] & ((A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in))))) |
          (B[2] & ((A[1] & B[1]) |
                   (A[1] & ((A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in))) |
                   (B[1] & ((A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in)))))), S[2]} ==
        ({1'b0, A[2]} + {1'b0, B[2]} +
         {1'b0, ((A[1] & B[1]) |
                 (A[1] & ((A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in))) |
                 (B[1] & ((A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in))))})
    );

    // Stage 3 matches a 1-bit full-adder fed by the bit 2 carry.
    check_stage3_add: assert property (
        @($global_clock)
        {C_out, S[3]} ==
        ({1'b0, A[3]} + {1'b0, B[3]} +
         {1'b0, ((A[2] & B[2]) |
                 (A[2] & ((A[1] & B[1]) |
                          (A[1] & ((A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in))) |
                          (B[1] & ((A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in))))) |
                 (B[2] & ((A[1] & B[1]) |
                          (A[1] & ((A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in))) |
                          (B[1] & ((A[0] & B[0]) | (A[0] & C_in) | (B[0] & C_in))))))})
    );

endmodule