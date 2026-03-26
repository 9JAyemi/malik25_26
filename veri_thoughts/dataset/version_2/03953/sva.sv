module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       C_in,
    input logic [3:0] S,
    input logic       C_out
);

    // Sampling clock only; RTL has no reset and is purely combinational.

    function automatic logic fa_sum (
        input logic a,
        input logic b,
        input logic cin
    );
        fa_sum = a ^ b ^ cin;
    endfunction

    function automatic logic fa_carry (
        input logic a,
        input logic b,
        input logic cin
    );
        fa_carry = (a & b) | (cin & (a ^ b));
    endfunction

    // Full 5-bit result matches A + B + C_in.
    check_total_sum: assert property (
        @(posedge clk) {C_out, S} == ({1'b0, A} + {1'b0, B} + C_in)
    );

    // Bit 0 sum matches the first full adder.
    check_sum_bit0: assert property (
        @(posedge clk) S[0] == fa_sum(A[0], B[0], C_in)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) S[1] == fa_sum(A[1], B[1], fa_carry(A[0], B[0], C_in))
    );

    // Bit 2 sum uses the carry from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) S[2] == fa_sum(
            A[2],
            B[2],
            fa_carry(A[1], B[1], fa_carry(A[0], B[0], C_in))
        )
    );

    // Bit 3 sum uses the carry from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) S[3] == fa_sum(
            A[3],
            B[3],
            fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], C_in)))
        )
    );

    // Carry out matches the final full-adder carry.
    check_carry_out: assert property (
        @(posedge clk) C_out == fa_carry(
            A[3],
            B[3],
            fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], C_in)))
        )
    );

    // Outputs stay stable when all inputs stay stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(C_in)) |-> ($stable(S) && $stable(C_out))
    );

    // S[0] depends only on A[0], B[0], and C_in.
    check_sum0_stable_when_local_inputs_stable: assert property (
        @(posedge clk) ($stable(A[0]) && $stable(B[0]) && $stable(C_in)) |-> $stable(S[0])
    );

    // S[1] depends only on A[1:0], B[1:0], and C_in.
    check_sum1_stable_when_lower_inputs_stable: assert property (
        @(posedge clk) ($stable(A[1:0]) && $stable(B[1:0]) && $stable(C_in)) |-> $stable(S[1])
    );

    // S[2] depends only on A[2:0], B[2:0], and C_in.
    check_sum2_stable_when_lower_inputs_stable: assert property (
        @(posedge clk) ($stable(A[2:0]) && $stable(B[2:0]) && $stable(C_in)) |-> $stable(S[2])
    );

endmodule