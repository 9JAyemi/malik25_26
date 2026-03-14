module r4_adder_sva (
    input  logic         clk,
    input  logic [3:0]   S,
    input  logic         Cout,
    input  logic [3:0]   A,
    input  logic [3:0]   B,
    input  logic         Cin
);
    // Sum and carry must match 5-bit addition of operands.
    check_sum_matches_five_bit_add: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Sum must equal low 4 bits of widened addition.
    check_sum_low_nibble: assert property (
        @(posedge clk) S == (({1'b0, A} + {1'b0, B} + Cin)[3:0])
    );

    // Cout must equal bit[4] (carry-out) of widened addition.
    check_cout_high_bit: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + Cin)[4])
    );

    // LSB sum bit equals XOR of A[0], B[0], and Cin.
    check_lsb_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Adding zeros yields S={000,Cin} and Cout=0.
    check_zero_plus_zero: assert property (
        @(posedge clk) (A == 4'd0 && B == 4'd0) |-> (S == {3'b000, Cin} && Cout == 1'b0)
    );

    // Adding zero with Cin=0 passes through A and Cout=0.
    check_add_zero_B: assert property (
        @(posedge clk) (B == 4'd0 && Cin == 1'b0) |-> (S == A && Cout == 1'b0)
    );

    // Adding zero with Cin=0 passes through B and Cout=0.
    check_add_zero_A: assert property (
        @(posedge clk) (A == 4'd0 && Cin == 1'b0) |-> (S == B && Cout == 1'b0)
    );

    // When B==0 and Cin==1, result is A+1 with carry only if A==0xF.
    check_increment_by_one: assert property (
        @(posedge clk) (B == 4'd0 && Cin == 1'b1) |-> (S == (A + 4'd1) && Cout == (A == 4'hF))
    );

    // When B is bitwise complement of A and Cin=0, sum is 0xF and no carry.
    check_complement_no_cin: assert property (
        @(posedge clk) (B == ~A && Cin == 1'b0) |-> (S == 4'hF && Cout == 1'b0)
    );

    // When B is bitwise complement of A and Cin=1, sum is 0x0 and carry=1.
    check_complement_with_cin: assert property (
        @(posedge clk) (B == ~A && Cin == 1'b1) |-> (S == 4'h0 && Cout == 1'b1)
    );
endmodule