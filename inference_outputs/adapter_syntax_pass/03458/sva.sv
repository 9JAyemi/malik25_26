module top_module_sva (
    input logic a1,
    input logic b1,
    input logic a2,
    input logic b2,
    input logic select,
    input logic [1:0] sum,
    input logic carry1,
    input logic carry2,
    input logic sum1,
    input logic sum2
);

    // adder1 sum is the XOR of its inputs with no carry-in.
    check_adder1_sum: assert property (
        @($global_clock) sum1 == (a1 ^ b1)
    );

    // adder1 carry-out matches the half-adder carry equation.
    check_adder1_carry: assert property (
        @($global_clock) carry1 == ((a1 & b1) | (1'b0 & (a1 ^ b1)))
    );

    // adder2 sum is the XOR of its inputs with no carry-in.
    check_adder2_sum: assert property (
        @($global_clock) sum2 == (a2 ^ b2)
    );

    // adder2 carry-out matches the half-adder carry equation.
    check_adder2_carry: assert property (
        @($global_clock) carry2 == ((a2 & b2) | (1'b0 & (a2 ^ b2)))
    );

    // sum[0] is the XOR of adder1 sum and adder2 sum.
    check_sum0_is_sum1_sum2: assert property (
        @($global_clock) sum[0] == (sum1 ^ sum2)
    );

    // sum[1] is the carry-out of the full-adder formed by the two half-adders.
    check_sum1_is_carry_out: assert property (
        @($global_clock) sum[1] == ((carry1 & carry2) | (carry1 & (sum1 ^ sum2)) | (carry2 & (sum1 ^ sum2)))
    );

    // When select is low, the top-level sum uses adder1 carry-out and adder2 sum.
    check_select_low_path: assert property (
        @($global_clock) !select |-> (sum == {carry2, (a1 ^ b1)})
    );

    // When select is high, the top-level sum uses adder2 carry-out and adder1 sum.
    check_select_high_path: assert property (
        @($global_clock) select |-> (sum == {carry1, (a2 ^ b2)})
    );

endmodule