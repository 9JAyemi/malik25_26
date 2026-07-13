module adder_4bit_sva (
    // Sampling clock for assertions (DUT has no clock/reset)
    input logic clk,
    // DUT ports
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);
    // Analysis: No clock/reset in RTL; purely combinational; S,Cout = A+B+Cin (5-bit)

    // Outputs form the exact 5-bit sum of A, B, and Cin.
    check_full_sum_correct: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // S equals the lower 4 bits of the 5-bit sum.
    check_sum_lower_bits_correct: assert property (
        @(posedge clk) S == ({1'b0, A} + {1'b0, B} + Cin)[3:0]
    );

    // Cout equals the MSB of the 5-bit sum.
    check_carry_out_msb_correct: assert property (
        @(posedge clk) Cout == ({1'b0, A} + {1'b0, B} + Cin)[4]
    );

    // Cout reflects overflow beyond 4 bits (sum >= 16).
    check_carry_threshold_equiv: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + Cin) >= 5'd16)
    );

    // With Cin = 0, outputs equal A + B.
    check_cin0_sum: assert property (
        @(posedge clk) (Cin == 1'b0) |-> ({Cout, S} == ({1'b0, A} + {1'b0, B}))
    );

    // With Cin = 1, outputs equal A + B + 1.
    check_cin1_sum: assert property (
        @(posedge clk) (Cin == 1'b1) |-> ({Cout, S} == ({1'b0, A} + {1'b0, B} + 5'd1))
    );

    // Zero add case: 0 + 0 + 0 => S=0, Cout=0.
    check_zero_case: assert property (
        @(posedge clk) ((A == 4'd0) && (B == 4'd0) && (Cin == 1'b0)) |-> ((S == 4'd0) && (Cout == 1'b0))
    );

    // Max add case: 15 + 15 + 1 => S=15, Cout=1.
    check_max_case: assert property (
        @(posedge clk) ((A == 4'd15) && (B == 4'd15) && (Cin == 1'b1)) |-> ((S == 4'd15) && (Cout == 1'b1))
    );

    // If inputs are unchanged from the previous cycle, outputs remain unchanged.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk)
        (($past(A,1,A) == A) && ($past(B,1,B) == B) && ($past(Cin,1,Cin) == Cin))
        |-> (($past(S,1,S) == S) && ($past(Cout,1,Cout) == Cout))
    );

endmodule