module min_max_sva #(
    parameter n = 8
)(
    input logic [n-1:0] in,
    input logic [n-1:0] min,
    input logic [n-1:0] max
);

    // min must be less than or equal to every input sample.
    check_min_le_input: assert property (
        @($global_clock) min <= in
    );

    // max must be greater than or equal to every input sample.
    check_max_ge_input: assert property (
        @($global_clock) max >= in
    );

    // min must be less than or equal to max.
    check_min_le_max: assert property (
        @($global_clock) min <= max
    );

    // If the sampled input is unchanged, the outputs must also be unchanged.
    check_stable_input_keeps_outputs_stable: assert property (
        @($global_clock) $stable(in) |-> ($stable(min) && $stable(max))
    );

    // If the sampled input is unchanged, the outputs must remain ordered.
    check_stable_input_keeps_order: assert property (
        @($global_clock) $stable(in) |-> (min <= max)
    );

    // If the sampled input is unchanged, min must remain less than or equal to max.
    check_stable_input_keeps_min_le_max: assert property (
        @($global_clock) $stable(in) |-> (min <= max)
    );

    // If the sampled input is unchanged, max must remain greater than or equal to min.
    check_stable_input_keeps_max_ge_min: assert property (
        @($global_clock) $stable(in) |-> (max >= min)
    );

    // If the sampled input is unchanged, min must remain less than or equal to every input sample.
    check_stable_input_keeps_min_le_input: assert property (
        @($global_clock) $stable(in) |-> (min <= in)
    );

    // If the sampled input is unchanged, max must remain greater than or equal to every input sample.
    check_stable_input_keeps_max_ge_input: assert property (
        @($global_clock) $stable(in) |-> (max >= in)
    );

endmodule