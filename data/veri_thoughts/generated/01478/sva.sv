module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout
);
    // DUT is combinational with no reset; assertions are sampled on CLK.

    // Sum/Cout equal the 5-bit addition of A, B, and Cin.
    check_sum_cout_matches_add: assert property (
        @(posedge CLK) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Sum is the low 4 bits of the full 5-bit addition.
    check_sum_low_nibble: assert property (
        @(posedge CLK) Sum == (({1'b0, A} + {1'b0, B} + Cin)[3:0])
    );

    // Cout is the MSB (bit 4) of the full 5-bit addition.
    check_cout_is_msb: assert property (
        @(posedge CLK) Cout == (({1'b0, A} + {1'b0, B} + Cin)[4])
    );

    // LSB of Sum equals XOR of operand LSBs and Cin.
    check_lsb_parity: assert property (
        @(posedge CLK) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // With Cin=0, result equals A+B with no increment.
    check_no_cin_behavior: assert property (
        @(posedge CLK) (Cin == 1'b0) |-> ({Cout, Sum} == ({1'b0, A} + {1'b0, B}))
    );

    // With Cin=1, result equals A+B plus one.
    check_with_cin_increment: assert property (
        @(posedge CLK) (Cin == 1'b1) |-> ({Cout, Sum} == ({1'b0, A} + {1'b0, B} + 5'd1))
    );

    // If A==0 and Cin==0, Sum mirrors B and Cout is 0.
    check_zero_A_no_cin: assert property (
        @(posedge CLK) ((A == 4'b0000) && (Cin == 1'b0)) |-> ((Sum == B) && (Cout == 1'b0))
    );

    // If B==0 and Cin==0, Sum mirrors A and Cout is 0.
    check_zero_B_no_cin: assert property (
        @(posedge CLK) ((B == 4'b0000) && (Cin == 1'b0)) |-> ((Sum == A) && (Cout == 1'b0))
    );

    // If A==0 and B==0, Sum equals Cin in bit0 and Cout is 0.
    check_only_cin_effect: assert property (
        @(posedge CLK) ((A == 4'b0000) && (B == 4'b0000)) |-> ((Sum == {3'b000, Cin}) && (Cout == 1'b0))
    );

    // Cout is 1 iff the full 5-bit sum exceeds 0xF.
    check_cout_overflow_flag: assert property (
        @(posedge CLK) Cout == (({1'b0, A} + {1'b0, B} + Cin) > 5'd15)
    );

endmodule