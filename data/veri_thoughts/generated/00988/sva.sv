module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout
);
    // Outputs must equal the 5-bit arithmetic sum of inputs.
    check_addition_result: assert property (
        @(posedge clk) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // LSB sum bit equals A[0] XOR B[0] XOR Cin.
    check_sum0_xor: assert property (
        @(posedge clk) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // When A and B are zero, Sum equals Cin in bit 0 and Cout is zero.
    check_zero_plus_zero: assert property (
        @(posedge clk) (A == 4'b0000 && B == 4'b0000) |-> (Sum == {3'b000, Cin} && Cout == 1'b0)
    );

    // With B==0 and Cin==0, Sum must equal A and Cout must be zero.
    check_add_B_zero_Cin_zero: assert property (
        @(posedge clk) (B == 4'b0000 && Cin == 1'b0) |-> (Sum == A && Cout == 1'b0)
    );

    // With A==0 and Cin==0, Sum must equal B and Cout must be zero.
    check_add_A_zero_Cin_zero: assert property (
        @(posedge clk) (A == 4'b0000 && Cin == 1'b0) |-> (Sum == B && Cout == 1'b0)
    );

    // Max + Max + Cin=1 yields Sum=0xF and Cout=1.
    check_fullscale_plus_fullscale_plus1: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF && Cin == 1'b1) |-> (Sum == 4'hF && Cout == 1'b1)
    );

    // Cout equals the MSB of the 5-bit sum.
    check_cout_matches_msb: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + Cin)[4])
    );

    // Sum equals the lower 4 bits of the 5-bit sum.
    check_sum_matches_lsb: assert property (
        @(posedge clk) Sum == (({1'b0, A} + {1'b0, B} + Cin)[3:0])
    );

    // If Cout is 0, the 5-bit sum must be <= 15 (no overflow).
    check_cout_zero_no_overflow: assert property (
        @(posedge clk) (Cout == 1'b0) |-> (({1'b0, A} + {1'b0, B} + Cin) <= 5'd15)
    );

    // If Cout is 1, the 5-bit sum must be >= 16 (overflow).
    check_cout_one_overflow: assert property (
        @(posedge clk) (Cout == 1'b1) |-> (({1'b0, A} + {1'b0, B} + Cin) >= 5'd16)
    );

    // With B==0xF and Cin=1, Sum must equal A and Cout must be 1.
    check_b_all_ones_plus_one: assert property (
        @(posedge clk) (B == 4'hF && Cin == 1'b1) |-> (Sum == A && Cout == 1'b1)
    );

    // With A==0xF and Cin=1, Sum must equal B and Cout must be 1.
    check_a_all_ones_plus_one: assert property (
        @(posedge clk) (A == 4'hF && Cin == 1'b1) |-> (Sum == B && Cout == 1'b1)
    );
endmodule