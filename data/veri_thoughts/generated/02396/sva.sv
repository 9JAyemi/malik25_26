module four_bit_adder_sva (
    input  logic        clk,
    input  logic        reset_n,
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        Cin,
    input  logic [3:0]  S,
    input  logic        Cout
);
    // Helper: expected 5-bit sum of A+B+Cin
    logic [4:0] expected_sum;
    assign expected_sum = A + B + Cin;

    // Helper: ripple carry chain derived from inputs
    logic c1, c2, c3;
    assign c1 = (A[0] & B[0]) | ((A[0] ^ B[0]) & Cin);
    assign c2 = (A[1] & B[1]) | ((A[1] ^ B[1]) & c1);
    assign c3 = (A[2] & B[2]) | ((A[2] ^ B[2]) & c2);

    // Sum and carry match arithmetic addition.
    check_full_sum_matches_addition: assert property (
        @(posedge clk) disable iff (!reset_n)
        {Cout, S} == expected_sum
    );

    // LSB sum is XOR of A[0], B[0], and Cin.
    check_bit0_sum_xor: assert property (
        @(posedge clk) disable iff (!reset_n)
        S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit1 sum equals XOR of A[1], B[1], and carry from bit0.
    check_bit1_sum_with_c1: assert property (
        @(posedge clk) disable iff (!reset_n)
        S[1] == (A[1] ^ B[1] ^ c1)
    );

    // Bit2 sum equals XOR of A[2], B[2], and carry from bit1.
    check_bit2_sum_with_c2: assert property (
        @(posedge clk) disable iff (!reset_n)
        S[2] == (A[2] ^ B[2] ^ c2)
    );

    // Bit3 sum equals XOR of A[3], B[3], and carry from bit2.
    check_bit3_sum_with_c3: assert property (
        @(posedge clk) disable iff (!reset_n)
        S[3] == (A[3] ^ B[3] ^ c3)
    );

    // Final carry-out equals ripple-carry from bit3.
    check_cout_ripple_formula: assert property (
        @(posedge clk) disable iff (!reset_n)
        Cout == ((A[3] & B[3]) | ((A[3] ^ B[3]) & c3))
    );

    // Outputs remain stable when inputs remain stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (!reset_n)
        $stable({A, B, Cin}) |-> $stable({S, Cout})
    );

    // Output change implies at least one input changed.
    check_output_change_implies_input_change: assert property (
        @(posedge clk) disable iff (!reset_n)
        !$stable({S, Cout}) |-> !$stable({A, B, Cin})
    );

    // Adding zero to zero yields Cout=0, S[3:1]=0, and S[0]=Cin.
    check_zero_plus_zero_behavior: assert property (
        @(posedge clk) disable iff (!reset_n)
        (A == 4'b0000 && B == 4'b0000) |-> (Cout == 1'b0) && (S[3:1] == 3'b000) && (S[0] == Cin)
    );

    // When both operands are max (0xF), carry-out must be 1 regardless of Cin.
    check_cout_high_when_both_max: assert property (
        @(posedge clk) disable iff (!reset_n)
        (A == 4'hF && B == 4'hF) |-> (Cout == 1'b1)
    );
endmodule