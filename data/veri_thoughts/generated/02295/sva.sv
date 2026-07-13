module four_bit_adder_sva (
    // Sampling clock/reset for assertions (RTL is purely combinational with no clock/reset)
    input logic CLK,
    input logic RESETn,

    // DUT ports
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       C_in,
    input logic [3:0] Sum,
    input logic       C_out
);
    ///// Functional correctness of 4-bit ripple-carry adder /////
    // Sum and C_out must equal the 5-bit result of A + B + C_in.
    check_full_sum_5bit: assert property (
        @(posedge CLK) disable iff (!RESETn)
        {C_out, Sum} == ({1'b0, A} + {1'b0, B} + {4'b0000, C_in})
    );

    // LSB sum equals XOR of A[0], B[0], and C_in.
    check_sum_bit0_xor: assert property (
        @(posedge CLK) disable iff (!RESETn)
        Sum[0] == (A[0] ^ B[0] ^ C_in)
    );

    // Bit1 sum equals XOR with carry from bit0.
    check_sum_bit1_ripple: assert property (
        @(posedge CLK) disable iff (!RESETn)
        Sum[1] == ((A[1] ^ B[1]) ^ ((A[0] & B[0]) | (B[0] & C_in) | (C_in & A[0])))
    );

    // Bit2 sum equals XOR with carry from bit1 ripple.
    check_sum_bit2_ripple: assert property (
        @(posedge CLK) disable iff (!RESETn)
        Sum[2] == (
            (A[2] ^ B[2]) ^
            (
                (A[1] & B[1]) |
                ((A[1] ^ B[1]) & ((A[0] & B[0]) | (B[0] & C_in) | (C_in & A[0])))
            )
        )
    );

    // Bit3 sum equals XOR with carry from bit2 ripple.
    check_sum_bit3_ripple: assert property (
        @(posedge CLK) disable iff (!RESETn)
        Sum[3] == (
            (A[3] ^ B[3]) ^
            (
                (A[2] & B[2]) |
                ((A[2] ^ B[2]) &
                    (
                        (A[1] & B[1]) |
                        ((A[1] ^ B[1]) & ((A[0] & B[0]) | (B[0] & C_in) | (C_in & A[0])))
                    )
                )
            )
        )
    );

    // Carry-out equals final ripple carry from bit3.
    check_cout_ripple: assert property (
        @(posedge CLK) disable iff (!RESETn)
        C_out == (
            (A[3] & B[3]) |
            ((A[3] ^ B[3]) &
                (
                    (A[2] & B[2]) |
                    ((A[2] ^ B[2]) &
                        (
                            (A[1] & B[1]) |
                            ((A[1] ^ B[1]) & ((A[0] & B[0]) | (B[0] & C_in) | (C_in & A[0])))
                        )
                    )
                )
            )
        )
    );

    // Carry-out equals MSB of the 5-bit sum.
    check_cout_is_msb: assert property (
        @(posedge CLK) disable iff (!RESETn)
        C_out == ({1'b0, A} + {1'b0, B} + {4'b0000, C_in})[4]
    );

    // When no overflow, C_out must be 0.
    check_no_overflow_implies_cout0: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (({1'b0, A} + {1'b0, B} + {4'b0000, C_in}) <= 5'd15) |-> (C_out == 1'b0)
    );

    // When overflow, C_out must be 1.
    check_overflow_implies_cout1: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (({1'b0, A} + {1'b0, B} + {4'b0000, C_in}) >= 5'd16) |-> (C_out == 1'b1)
    );

    // Identity: adding zero B preserves A (plus C_in).
    check_zero_B_identity: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (B == 4'd0) |-> ({C_out, Sum} == ({1'b0, A} + {4'b0000, C_in}))
    );

    // Identity: adding zero A preserves B (plus C_in).
    check_zero_A_identity: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (A == 4'd0) |-> ({C_out, Sum} == ({1'b0, B} + {4'b0000, C_in}))
    );

    // Combinational: if inputs are unchanged cycle-to-cycle, outputs remain unchanged.
    check_purely_combinational: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ($stable(A) && $stable(B) && $stable(C_in)) |-> ($stable(Sum) && $stable(C_out))
    );
endmodule