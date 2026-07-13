module adder_sva (
    input logic CLK,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] sum
);
    // sum equals A + B (8-bit wraparound).
    check_sum_matches_add: assert property (
        @(posedge CLK) sum == (({1'b0, A} + {1'b0, B})[7:0])
    );

    // When A is zero, sum equals B.
    check_sum_when_A_zero: assert property (
        @(posedge CLK) (A == 8'h00) |-> (sum == B)
    );

    // When B is zero, sum equals A.
    check_sum_when_B_zero: assert property (
        @(posedge CLK) (B == 8'h00) |-> (sum == A)
    );

    // LSB of sum equals XOR of LSBs of A and B.
    check_bit0_xor: assert property (
        @(posedge CLK) sum[0] == (A[0] ^ B[0])
    );

    // If inputs hold their values, sum holds its value.
    check_sum_stable_when_inputs_stable: assert property (
        @(posedge CLK) (A == $past(A) && B == $past(B)) |-> (sum == $past(sum))
    );

    // If sum changed, at least one input changed.
    check_inputs_change_if_sum_changes: assert property (
        @(posedge CLK) (sum != $past(sum)) |-> ((A != $past(A)) || (B != $past(B)))
    );
endmodule