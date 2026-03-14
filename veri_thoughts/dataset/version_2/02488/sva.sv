module ripple_carry_adder_sva (
    input logic CLK,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic Cin,
    input logic [15:0] Sum
);
    // Sum equals (A + B + Cin) modulo 2^16 each cycle.
    check_sum_matches_addition: assert property (
        @(posedge CLK) Sum == ({1'b0, A} + {1'b0, B} + Cin)[15:0]
    );

    // LSB sum equals A[0] XOR B[0] XOR Cin.
    check_lsb_xor: assert property (
        @(posedge CLK) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Adding zero operand B with Cin=0 yields Sum = A.
    check_zero_plus_A: assert property (
        @(posedge CLK) (B == 16'h0000 && Cin == 1'b0) |-> (Sum == A)
    );

    // Adding zero operand A with Cin=0 yields Sum = B.
    check_zero_plus_B: assert property (
        @(posedge CLK) (A == 16'h0000 && Cin == 1'b0) |-> (Sum == B)
    );

    // Adding zeros yields Sum = Cin on bit0 and zeros elsewhere.
    check_zero_plus_zero: assert property (
        @(posedge CLK) (A == 16'h0000 && B == 16'h0000) |-> (Sum == {15'b0, Cin})
    );

    // A + ~A with Cin=0 yields all ones.
    check_complement_no_cin_allones: assert property (
        @(posedge CLK) (B == ~A && Cin == 1'b0) |-> (Sum == 16'hFFFF)
    );

    // A + ~A with Cin=1 yields zero.
    check_complement_with_cin_zero: assert property (
        @(posedge CLK) (B == ~A && Cin == 1'b1) |-> (Sum == 16'h0000)
    );

    // When A == B and Cin=0, the result is even so LSB is 0.
    check_equal_operands_no_cin_lsb0: assert property (
        @(posedge CLK) (A == B && Cin == 1'b0) |-> (Sum[0] == 1'b0)
    );

    // When A == B and Cin=1, the result is odd so LSB is 1.
    check_equal_operands_with_cin_lsb1: assert property (
        @(posedge CLK) (A == B && Cin == 1'b1) |-> (Sum[0] == 1'b1)
    );

    // If inputs are stable cycle-to-cycle, Sum is also stable.
    check_stable_inputs_imply_stable_sum: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(Cin)) |-> $stable(Sum)
    );
endmodule