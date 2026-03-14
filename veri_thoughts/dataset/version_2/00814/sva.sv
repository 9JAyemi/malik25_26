module ripple_carry_adder_sva(
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout
);
    // Overall 5-bit result equals A + B + Cin.
    check_total_sum_matches_addition: assert property (
        @(posedge clk) {Cout, Sum} == (A + B + Cin)
    );

    // LSB sum equals A[0] XOR B[0] XOR Cin.
    check_sum_bit0_xor: assert property (
        @(posedge clk) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit1 sum equals XOR with carry from bit0.
    check_sum_bit1_from_carry0: assert property (
        @(posedge clk) Sum[1] == (
            A[1] ^ B[1] ^ ( (A[0] & B[0]) | ( Cin & (A[0] ^ B[0]) ) )
        )
    );

    // Bit2 sum equals XOR with carry from bit1.
    check_sum_bit2_from_carry1: assert property (
        @(posedge clk) Sum[2] == (
            A[2] ^ B[2] ^ (
                (A[1] & B[1]) |
                ( ((A[0] & B[0]) | ( Cin & (A[0] ^ B[0]) )) & (A[1] ^ B[1]) )
            )
        )
    );

    // Bit3 sum equals XOR with carry from bit2.
    check_sum_bit3_from_carry2: assert property (
        @(posedge clk) Sum[3] == (
            A[3] ^ B[3] ^ (
                (A[2] & B[2]) |
                ( ((A[1] & B[1]) | ( ((A[0] & B[0]) | ( Cin & (A[0] ^ B[0]) )) & (A[1] ^ B[1]) )) & (A[2] ^ B[2]) )
            )
        )
    );

    // Final carry-out equals generate/propagate from bit3.
    check_cout_from_carry2: assert property (
        @(posedge clk) Cout == (
            (A[3] & B[3]) |
            ( (
                (A[2] & B[2]) |
                ( ((A[1] & B[1]) | ( ((A[0] & B[0]) | ( Cin & (A[0] ^ B[0]) )) & (A[1] ^ B[1]) )) & (A[2] ^ B[2]) )
            ) & (A[3] ^ B[3]) )
        )
    );

    // Lower 2 sum bits match 2-bit addition of A,B and Cin.
    check_lower2bits_addition: assert property (
        @(posedge clk) Sum[1:0] == (A[1:0] + B[1:0] + Cin)[1:0]
    );

    // Lower 3 sum bits match 3-bit addition of A,B and Cin.
    check_lower3bits_addition: assert property (
        @(posedge clk) Sum[2:0] == (A[2:0] + B[2:0] + Cin)[2:0]
    );

    // Outputs do not change when inputs are stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({A,B,Cin}) |-> $stable({Sum,Cout})
    );

    // When B=0 and Cin=0, output equals A and Cout=0.
    check_identity_B_zero_Cin_zero: assert property (
        @(posedge clk) ((B == 4'b0000) && (Cin == 1'b0)) |-> ((Sum == A) && (Cout == 1'b0))
    );
endmodule