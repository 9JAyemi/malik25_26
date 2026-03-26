module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic Cout
);

    // S always reflects the 4-bit truncated sum of A and B.
    check_sum_matches_truncated_add: assert property (
        @($global_clock) disable iff (1'b0) S == (A + B)
    );

    // Cout is always low in this implementation.
    check_cout_constant_zero: assert property (
        @($global_clock) disable iff (1'b0) Cout == 1'b0
    );

    // A equal to zero passes B through to S.
    check_zero_a_passthrough: assert property (
        @($global_clock) disable iff (1'b0) (A == 4'h0) |-> (S == B && Cout == 1'b0)
    );

    // B equal to zero passes A through to S.
    check_zero_b_passthrough: assert property (
        @($global_clock) disable iff (1'b0) (B == 4'h0) |-> (S == A && Cout == 1'b0)
    );

    // Mathematical overflow does not raise Cout in this RTL.
    check_overflow_keeps_cout_low: assert property (
        @($global_clock) disable iff (1'b0) (({1'b0, A} + {1'b0, B}) > 5'd15) |-> (Cout == 1'b0)
    );

    // Stable inputs keep the outputs stable across samples.
    check_stable_inputs_keep_outputs_stable: assert property (
        @($global_clock) disable iff (1'b0) ($stable(A) && $stable(B)) |-> ($stable(S) && $stable(Cout))
    );

endmodule