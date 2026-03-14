module add_two_signals_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] sum,
    input logic carry_out
);
    // {carry_out,sum} equals the 5-bit sum of A and B.
    check_combined_sum: assert property (
        @(posedge clk) {carry_out, sum} == ({1'b0, A} + {1'b0, B})
    );

    // carry_out is the MSB of the 5-bit sum A+B.
    check_carry_msb: assert property (
        @(posedge clk) carry_out == (({1'b0, A} + {1'b0, B})[4])
    );

    // sum is the low 4 bits of the 5-bit sum A+B.
    check_sum_low_bits: assert property (
        @(posedge clk) sum == (({1'b0, A} + {1'b0, B})[3:0])
    );

    // Adding zero on B passes A through with no carry.
    check_zero_B_identity: assert property (
        @(posedge clk) (B == 4'd0) |-> (sum == A && carry_out == 1'b0)
    );

    // Adding zero on A passes B through with no carry.
    check_zero_A_identity: assert property (
        @(posedge clk) (A == 4'd0) |-> (sum == B && carry_out == 1'b0)
    );

    // If inputs are stable across cycles, outputs are stable as well.
    check_hold_behavior: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable({carry_out, sum})
    );

    // Carry-out iff modulo-16 sum wrapped below at least one operand.
    check_carry_wraparound: assert property (
        @(posedge clk) carry_out == ((sum < A) || (sum < B))
    );
endmodule