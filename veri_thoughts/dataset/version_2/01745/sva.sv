module adder_4bit_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic Cout
);
    // Local reference computations for expected results
    wire [4:0] sum5 = {1'b0, A} + {1'b0, B};
    wire       c0   = (A[0] & B[0]);
    wire       c1   = (A[1] & B[1]) | (A[1] & c0) | (B[1] & c0);
    wire       c2   = (A[2] & B[2]) | (A[2] & c1) | (B[2] & c1);

    // Sum and carry-out equal 5-bit addition of A and B with zero carry-in.
    check_addition_exact: assert property (
        @(posedge CLK) {Cout, S} == sum5
    );

    // Sum vector matches lower 4 bits of the 5-bit addition.
    check_sum_bits_match: assert property (
        @(posedge CLK) S == sum5[3:0]
    );

    // Carry-out matches MSB of the 5-bit addition.
    check_cout_match: assert property (
        @(posedge CLK) Cout == sum5[4]
    );

    // LSB sum equals XOR of A[0] and B[0] (zero Cin).
    check_lsb_sum: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0])
    );

    // Bit1 sum equals XOR with carry from bit0.
    check_bit1_sum: assert property (
        @(posedge CLK) S[1] == (A[1] ^ B[1] ^ c0)
    );

    // Bit2 sum equals XOR with carry from bit1.
    check_bit2_sum: assert property (
        @(posedge CLK) S[2] == (A[2] ^ B[2] ^ c1)
    );

    // Bit3 sum equals XOR with carry from bit2.
    check_bit3_sum: assert property (
        @(posedge CLK) S[3] == (A[3] ^ B[3] ^ c2)
    );

    // Carry-out equals majority of A[3], B[3], and carry from bit2.
    check_cout_from_bit3: assert property (
        @(posedge CLK) Cout == ((A[3] & B[3]) | (A[3] & c2) | (B[3] & c2))
    );

    // Adding zero on B passes A through with no carry.
    check_add_zero_B: assert property (
        @(posedge CLK) (B == 4'h0) |-> (S == A) && (Cout == 1'b0)
    );

    // Adding zero on A passes B through with no carry.
    check_add_zero_A: assert property (
        @(posedge CLK) (A == 4'h0) |-> (S == B) && (Cout == 1'b0)
    );

    // 0xF + 0xF yields 0xE with carry-out 1.
    check_full_max_case: assert property (
        @(posedge CLK) (A == 4'hF && B == 4'hF) |-> (S == 4'hE) && (Cout == 1'b1)
    );

    // If inputs are stable across cycles, outputs remain stable.
    check_output_stability: assert property (
        @(posedge CLK) ($stable(A) && $stable(B)) |-> ($stable(S) && $stable(Cout))
    );
endmodule