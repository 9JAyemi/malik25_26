module adder4bit_sva(
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);

    // Combined carry and sum must match 4-bit addition with carry-in.
    check_full_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, Cin})
    );

    // Bit 0 sum must implement the full-adder XOR equation.
    check_bit0_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Lower two sum bits must match the 2-bit addition result.
    check_low2_sum: assert property (
        @(posedge clk) S[1:0] == (A[1:0] + B[1:0] + Cin)
    );

    // Lower three sum bits must match the 3-bit addition result.
    check_low3_sum: assert property (
        @(posedge clk) S[2:0] == (A[2:0] + B[2:0] + Cin)
    );

    // Zero B and zero carry-in must pass A through with no carry-out.
    check_b_zero_passthrough: assert property (
        @(posedge clk) ((B == 4'b0000) && (Cin == 1'b0)) |-> ((S == A) && (Cout == 1'b0))
    );

    // Zero A and zero carry-in must pass B through with no carry-out.
    check_a_zero_passthrough: assert property (
        @(posedge clk) ((A == 4'b0000) && (Cin == 1'b0)) |-> ((S == B) && (Cout == 1'b0))
    );

    // Zero A and zero B must pass Cin into the least-significant sum bit only.
    check_cin_only_behavior: assert property (
        @(posedge clk) ((A == 4'b0000) && (B == 4'b0000)) |-> ((S == {3'b000, Cin}) && (Cout == 1'b0))
    );

    // Carry-out must be asserted exactly when the 5-bit sum exceeds 15.
    check_cout_threshold: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + {4'b0000, Cin}) > 5'd15)
    );

endmodule