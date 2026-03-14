module four_bit_adder_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic C_in,
    input logic [3:0] S,
    input logic C_out
);
    // Sum and carry must equal 5-bit addition of inputs.
    check_total_sum: assert property (
        @(posedge CLK) disable iff (!RESETn) {C_out, S} == ({1'b0, A} + {1'b0, B} + C_in)
    );

    // LSB sum equals XOR of A[0], B[0], and C_in.
    check_lsb_sum: assert property (
        @(posedge CLK) disable iff (!RESETn) S[0] == (A[0] ^ B[0] ^ C_in)
    );

    // Low 2-bit sum matches truncated 2-bit addition.
    check_low2_trunc: assert property (
        @(posedge CLK) disable iff (!RESETn) S[1:0] == (({1'b0, A[1:0]} + {1'b0, B[1:0]} + C_in)[1:0])
    );

    // Low 3-bit sum matches truncated 3-bit addition.
    check_low3_trunc: assert property (
        @(posedge CLK) disable iff (!RESETn) S[2:0] == (({1'b0, A[2:0]} + {1'b0, B[2:0]} + C_in)[2:0])
    );

    // Carry-out equals MSB of the 5-bit total sum.
    check_cout_msb_equal: assert property (
        @(posedge CLK) disable iff (!RESETn) C_out == (({1'b0, A} + {1'b0, B} + C_in)[4])
    );

    // Bit1 sum uses carry from bit0 result.
    check_s1_with_carry0: assert property (
        @(posedge CLK) disable iff (!RESETn) S[1] == (A[1] ^ B[1] ^ (({1'b0, A[0]} + {1'b0, B[0]} + C_in)[1]))
    );

    // Bit2 sum uses carry from bit1 result.
    check_s2_with_carry1: assert property (
        @(posedge CLK) disable iff (!RESETn) S[2] == (A[2] ^ B[2] ^ (({1'b0, A[1:0]} + {1'b0, B[1:0]} + C_in)[2]))
    );

    // Bit3 sum uses carry from bit2 result.
    check_s3_with_carry2: assert property (
        @(posedge CLK) disable iff (!RESETn) S[3] == (A[3] ^ B[3] ^ (({1'b0, A[2:0]} + {1'b0, B[2:0]} + C_in)[3]))
    );

    // MSB carry-out equals full-adder formula using carry into MSB.
    check_cout_full_adder_msb: assert property (
        @(posedge CLK) disable iff (!RESETn) C_out == ( (A[3] & B[3]) | ((A[3] ^ B[3]) & (({1'b0, A[2:0]} + {1'b0, B[2:0]} + C_in)[3])) )
    );

    // High 2-bit block plus propagated carry equals outputs' high block and C_out.
    check_high_group_with_carry2: assert property (
        @(posedge CLK) disable iff (!RESETn) {C_out, S[3:2]} == ( {1'b0, A[3:2]} + {1'b0, B[3:2]} + (({1'b0, A[2:0]} + {1'b0, B[2:0]} + C_in)[3]) )
    );

    // Adding zero B and zero C_in returns A, with no carry.
    identity_B0_C0: assert property (
        @(posedge CLK) disable iff (!RESETn) ((B == 4'b0000) && (C_in == 1'b0)) |-> ((S == A) && (C_out == 1'b0))
    );

    // Adding zero A and zero C_in returns B, with no carry.
    identity_A0_C0: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A == 4'b0000) && (C_in == 1'b0)) |-> ((S == B) && (C_out == 1'b0))
    );

    // Adding only C_in to zero A and zero B places C_in in bit0, no carry-out.
    identity_A0_B0: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A == 4'b0000) && (B == 4'b0000)) |-> ((S == {3'b000, C_in}) && (C_out == 1'b0))
    );

    // Max plus one case: 0xF + 0xF + 1 = carry 1 and 0xF.
    max_plus_one_case: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A == 4'hF) && (B == 4'hF) && (C_in == 1'b1)) |-> ((S == 4'hF) && (C_out == 1'b1))
    );
endmodule