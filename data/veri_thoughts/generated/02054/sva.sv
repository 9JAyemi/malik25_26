module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] C,
    input logic Cout
);

    // Outputs represent the 5-bit sum of inputs.
    check_sum_match: assert property (
        @(posedge CLK) {Cout, C} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Lower 4 bits equal the truncated sum.
    check_lower_nibble: assert property (
        @(posedge CLK) C == ({1'b0, A} + {1'b0, B} + Cin)[3:0]
    );

    // Carry-out equals the MSB of the 5-bit sum.
    check_cout_msb: assert property (
        @(posedge CLK) Cout == ({1'b0, A} + {1'b0, B} + Cin)[4]
    );

    // Carry-out flags overflow beyond 4 bits.
    check_cout_overflow_flag: assert property (
        @(posedge CLK) Cout == (({1'b0, A} + {1'b0, B} + Cin) > 5'd15)
    );

    // If inputs are stable across cycles, outputs are stable as well.
    check_stable_io: assert property (
        @(posedge CLK) $stable({A, B, Cin}) |=> $stable({C, Cout})
    );

    // With B=0 and Cin=0, output equals A and no carry.
    check_identity_B0_Cin0: assert property (
        @(posedge CLK) ((B == 4'b0000) && (Cin == 1'b0)) |=> (C == A && Cout == 1'b0)
    );

    // With A=0 and B=0, output equals Cin and no carry.
    check_identity_A0_B0: assert property (
        @(posedge CLK) ((A == 4'b0000) && (B == 4'b0000)) |=> (C == {3'b000, Cin} && Cout == 1'b0)
    );

    // With Cin=0, result equals A+B with no extra bias.
    check_cin0_add: assert property (
        @(posedge CLK) (Cin == 1'b0) |=> ({Cout, C} == ({1'b0, A} + {1'b0, B}))
    );

    // LSB is XOR of input bits and carry-in.
    check_lsb_full_adder: assert property (
        @(posedge CLK) C[0] == (A[0] ^ B[0] ^ Cin)
    );

    // When carry-out is 1, adding 16 to C reproduces the 5-bit sum.
    check_wrap_on_carry: assert property (
        @(posedge CLK) (Cout == 1'b1) |=> ({1'b0, C} + 5'd16 == ({1'b0, A} + {1'b0, B} + Cin))
    );

    // Max case: 15+15+1 produces C=15 and Cout=1.
    check_max_case: assert property (
        @(posedge CLK) ((A == 4'hF) && (B == 4'hF) && (Cin == 1'b1)) |=> ((C == 4'hF) && (Cout == 1'b1))
    );

endmodule