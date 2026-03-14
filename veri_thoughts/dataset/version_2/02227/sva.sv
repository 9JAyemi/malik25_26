module four_bit_adder_sva (
    input logic clk,          // Verification clock (DUT has no clock/reset)
    input logic [3:0] A,      // DUT input
    input logic [3:0] B,      // DUT input
    input logic [3:0] Y       // DUT output
);
    // DUT is purely combinational ripple-carry adder: Y == (A + B) modulo 16.

    // Local expected carry chain from A and B (mirrors DUT full_adder equations)
    logic c0, c1, c2;
    assign c0 = A[0] & B[0];
    assign c1 = (A[1] & B[1]) | (A[1] & c0) | (B[1] & c0);
    assign c2 = (A[2] & B[2]) | (A[2] & c1) | (B[2] & c1);

    // Y equals the 4-bit sum of A and B (lower 4 bits).
    check_sum_mod16: assert property (
        @(posedge clk) Y == (A + B)
    );

    // LSB sum is XOR of A[0] and B[0] (carry_in=0).
    check_bit0_sum: assert property (
        @(posedge clk) Y[0] == (A[0] ^ B[0])
    );

    // Bit1 sum uses carry from bit0.
    check_bit1_sum: assert property (
        @(posedge clk) Y[1] == (A[1] ^ B[1] ^ c0)
    );

    // Bit2 sum uses carry1 from bit1/c0.
    check_bit2_sum: assert property (
        @(posedge clk) Y[2] == (A[2] ^ B[2] ^ c1)
    );

    // Bit3 sum uses carry2 from bit2/c1.
    check_bit3_sum: assert property (
        @(posedge clk) Y[3] == (A[3] ^ B[3] ^ c2)
    );

    // Adding zero on B passes A through.
    check_zero_B_passthrough: assert property (
        @(posedge clk) (B == 4'b0000) |-> (Y == A)
    );

    // Adding zero on A passes B through.
    check_zero_A_passthrough: assert property (
        @(posedge clk) (A == 4'b0000) |-> (Y == B)
    );

    // Commutativity: result matches B + A as well.
    check_commutativity: assert property (
        @(posedge clk) Y == (B + A)
    );

    // Adding 1 on B increments A modulo 16.
    check_increment_when_B_is_1: assert property (
        @(posedge clk) (B == 4'b0001) |-> (Y == (A + 4'd1))
    );

    // If A and B are unchanged cycle-to-cycle, Y is unchanged.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) (A == $past(A) && B == $past(B)) |-> (Y == $past(Y))
    );

endmodule