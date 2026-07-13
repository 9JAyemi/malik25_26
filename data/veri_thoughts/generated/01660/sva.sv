module adder_4bit_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);
    // DUT has no clock/reset; pure combinational adder. Assertions sample on external CLK.

    // S equals the low 4 bits of A + B + Cin.
    check_sum_lowbits: assert property (
        @(posedge CLK) S == (A + B + Cin)[3:0]
    );

    // Cout equals the carry-out bit of A + B + Cin.
    check_cout_bit: assert property (
        @(posedge CLK) Cout == (A + B + Cin)[4]
    );

    // LSB sum equals XOR of A[0], B[0], and Cin.
    check_lsb_xor: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Adding zero (B=0 and Cin=0) passes A through with no carry.
    check_identity_when_B_zero: assert property (
        @(posedge CLK) ((B == 4'b0000) && (Cin == 1'b0)) |-> (S == A) && (Cout == 1'b0)
    );

    // Adding zero (A=0 and Cin=0) passes B through with no carry.
    check_identity_when_A_zero: assert property (
        @(posedge CLK) ((A == 4'b0000) && (Cin == 1'b0)) |-> (S == B) && (Cout == 1'b0)
    );

    // With A=0 and B=0, sum is Cin in bit0 and no carry.
    check_only_cin: assert property (
        @(posedge CLK) ((A == 4'b0000) && (B == 4'b0000)) |-> (S == {3'b000, Cin}) && (Cout == 1'b0)
    );

    // With A=0xF, B=0xF, Cin=0: sum=0xE and carry=1.
    check_max_operands_no_cin: assert property (
        @(posedge CLK) ((A == 4'hF) && (B == 4'hF) && (Cin == 1'b0)) |-> (S == 4'hE) && (Cout == 1'b1)
    );

    // With A=0xF, B=0xF, Cin=1: sum=0xF and carry=1.
    check_max_operands_with_cin: assert property (
        @(posedge CLK) ((A == 4'hF) && (B == 4'hF) && (Cin == 1'b1)) |-> (S == 4'hF) && (Cout == 1'b1)
    );

    // If inputs are stable across cycles, outputs remain stable.
    check_stable_outputs_when_inputs_stable: assert property (
        @(posedge CLK) $stable({A,B,Cin}) |-> $stable({S,Cout})
    );

    // Carry-out equals overflow comparison of A + B + Cin.
    check_cout_overflow_match: assert property (
        @(posedge CLK) Cout == ((A + B + Cin) >= 5'd16)
    );

endmodule