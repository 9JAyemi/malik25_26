module top_module_sva (
    input logic a,
    input logic b,
    input logic out
);

    // Output must equal the AND of the two inputs.
    check_out_matches_and: assert property (
        @($global_clock) out == (a & b)
    );

    // Both inputs high must drive the output high.
    check_both_inputs_high_drive_out_high: assert property (
        @($global_clock) (a & b) |-> out
    );

    // A low on input a must force the output low.
    check_a_low_forces_out_low: assert property (
        @($global_clock) !a |-> !out
    );

    // A low on input b must force the output low.
    check_b_low_forces_out_low: assert property (
        @($global_clock) !b |-> !out
    );

    // A high output requires both inputs to be high.
    check_out_high_requires_both_inputs_high: assert property (
        @($global_clock) out |-> (a & b)
    );

endmodule

bind top_module top_module_sva top_module_sva_inst (
    .a(a),
    .b(b),
    .out(out)
);