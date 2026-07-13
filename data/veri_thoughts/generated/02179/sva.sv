module add4bit_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] sum,
    input logic carry_out
);
    // carry_out is hardwired to 0 (LSB of {and_out,1'b0}).
    check_carry_out_const_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (carry_out == 1'b0)
    );

    // sum equals (A ^ B) + carry_out (lower 4 bits).
    check_sum_eq_xor_plus_carry: assert property (
        @(posedge CLK) disable iff (!RESETn) (sum == ((A ^ B) + carry_out)[3:0])
    );

    // With carry_out == 0, sum equals bitwise XOR of A and B.
    check_sum_eq_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) (sum == (A ^ B))
    );

    // When A equals B, sum must be zero (XOR property).
    check_sum_zero_when_A_eq_B: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == B) |-> (sum == 4'b0000)
    );

    // When A is zero, sum must equal B (XOR with zero).
    check_sum_eq_B_when_A_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 4'b0000) |-> (sum == B)
    );

    // When B is zero, sum must equal A (XOR with zero).
    check_sum_eq_A_when_B_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (B == 4'b0000) |-> (sum == A)
    );

    // When A is bitwise NOT of B, sum must be all ones.
    check_sum_all_ones_when_A_is_bitwise_not_B: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == ~B) |-> (sum == 4'hF)
    );

    // Outputs remain stable if inputs are stable (purely combinational).
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) ($stable(A) && $stable(B)) |-> ($stable(sum) && $stable(carry_out))
    );
endmodule