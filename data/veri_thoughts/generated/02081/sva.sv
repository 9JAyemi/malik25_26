module xor_gate_sva (
    input logic CLK,          // sampling clock for SVA
    input logic a,
    input logic b,
    input logic out_if_else
);
    // Output equals XOR of inputs.
    check_out_matches_xor: assert property (
        @(posedge CLK) out_if_else == (a ^ b)
    );

    // Output is 1 when inputs differ.
    check_out_one_when_inputs_differ: assert property (
        @(posedge CLK) (a != b) |-> (out_if_else == 1'b1)
    );

    // Output is 0 when inputs are equal.
    check_out_zero_when_inputs_equal: assert property (
        @(posedge CLK) (a == b) |-> (out_if_else == 1'b0)
    );

    // If inputs are stable, output remains stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable(a) && $stable(b) |-> $stable(out_if_else)
    );

    // If only a changes between cycles, output changes.
    check_output_changes_when_only_a_changes: assert property (
        @(posedge CLK) $changed(a) && $stable(b) |-> $changed(out_if_else)
    );

    // If only b changes between cycles, output changes.
    check_output_changes_when_only_b_changes: assert property (
        @(posedge CLK) $changed(b) && $stable(a) |-> $changed(out_if_else)
    );
endmodule