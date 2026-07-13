module addition_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [8:0] result
);

    // Result equals the zero-extended sum of the two inputs.
    check_result_matches_sum: assert property (
        @($global_clock) result == ({1'b0, a} + {1'b0, b})
    );

    // Zero plus zero produces zero.
    check_zero_inputs: assert property (
        @($global_clock) (a == 8'h00 && b == 8'h00) |-> (result == 9'h000)
    );

    // Adding zero on b passes a through unchanged.
    check_b_zero_passthrough: assert property (
        @($global_clock) (b == 8'h00) |-> (result == {1'b0, a})
    );

    // Adding zero on a passes b through unchanged.
    check_a_zero_passthrough: assert property (
        @($global_clock) (a == 8'h00) |-> (result == {1'b0, b})
    );

    // Stable inputs keep the combinational result stable.
    check_stable_inputs_stable_result: assert property (
        @($global_clock) ($stable(a) && $stable(b)) |-> $stable(result)
    );

    // Maximum inputs produce the maximum 9-bit sum.
    check_max_inputs_sum: assert property (
        @($global_clock) (a == 8'hFF && b == 8'hFF) |-> (result == 9'h1FE)
    );

endmodule