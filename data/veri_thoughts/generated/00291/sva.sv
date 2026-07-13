module top_module_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic cin,
    input logic select,
    input logic [3:0] out
);

    // Output must always match the muxed adder-or-constant function.
    check_mux_function: assert property (
        @($global_clock) out == (select ? (A + B + cin) : 4'hF)
    );

    // When select is low, the output must be the constant value.
    check_select_low_constant: assert property (
        @($global_clock) !select |-> (out == 4'hF)
    );

    // When select is high, the output must be the 4-bit adder result.
    check_select_high_sum: assert property (
        @($global_clock) select |-> (out == (A + B + cin))
    );

    // A rising select must make the output reflect the adder result.
    check_select_rise_updates_sum: assert property (
        @($global_clock) $rose(select) |-> (out == (A + B + cin))
    );

    // A falling select must make the output return to the constant value.
    check_select_fall_updates_constant: assert property (
        @($global_clock) $fell(select) |-> (out == 4'hF)
    );

    // If all inputs are stable, the output must remain stable.
    check_stable_inputs_stable_output: assert property (
        @($global_clock) $stable({A, B, cin, select}) |-> $stable(out)
    );

    // With B and cin at zero, selecting the adder must pass A through.
    check_zero_b_passthrough_a: assert property (
        @($global_clock) select && (B == 4'h0) && !cin |-> (out == A)
    );

    // With A and cin at zero, selecting the adder must pass B through.
    check_zero_a_passthrough_b: assert property (
        @($global_clock) select && (A == 4'h0) && !cin |-> (out == B)
    );

endmodule