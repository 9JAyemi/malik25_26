module xor_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out
);
    // Output equals XOR of inputs each cycle.
    check_xor_function: assert property (
        @(posedge clk) out == (a ^ b)
    );

    // When inputs are equal, output is 0.
    check_out_zero_when_inputs_equal: assert property (
        @(posedge clk) (a == b) |-> (out == 1'b0)
    );

    // When inputs differ, output is 1.
    check_out_one_when_inputs_differ: assert property (
        @(posedge clk) (a != b) |-> (out == 1'b1)
    );

    // Output change equals parity of input changes (exactly one input change causes output change).
    check_change_parity_relation: assert property (
        @(posedge clk) ($changed(out) == ($changed(a) ^ $changed(b)))
    );

    // If only 'a' changes, output changes.
    check_out_changes_on_a_only: assert property (
        @(posedge clk) ($changed(a) && !$changed(b)) |-> $changed(out)
    );

    // If only 'b' changes, output changes.
    check_out_changes_on_b_only: assert property (
        @(posedge clk) (!$changed(a) && $changed(b)) |-> $changed(out)
    );

    // If both inputs change, output does not change.
    check_out_stable_on_both_change: assert property (
        @(posedge clk) ($changed(a) && $changed(b)) |-> !$changed(out)
    );

    // If both inputs are stable, output is stable.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> $stable(out)
    );

    // Truth table: a=0,b=0 => out=0.
    check_tt_00: assert property (
        @(posedge clk) (!a && !b) |-> (out == 1'b0)
    );

    // Truth table: a=1,b=0 => out=1.
    check_tt_10: assert property (
        @(posedge clk) (a && !b) |-> (out == 1'b1)
    );

    // Truth table: a=0,b=1 => out=1.
    check_tt_01: assert property (
        @(posedge clk) (!a && b) |-> (out == 1'b1)
    );

    // Truth table: a=1,b=1 => out=0.
    check_tt_11: assert property (
        @(posedge clk) (a && b) |-> (out == 1'b0)
    );
endmodule