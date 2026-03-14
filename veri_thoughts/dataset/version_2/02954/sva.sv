module and_gate_sva (
    input logic a,
    input logic b,
    input logic out
);
    // Combinational AND gate; no clock/reset present; sample on $global_clock.

    // out must equal a & b every cycle.
    check_out_is_and: assert property (
        @(posedge $global_clock) out == (a & b)
    );

    // If out is HIGH, both inputs must be HIGH.
    check_out_high_requires_inputs_high: assert property (
        @(posedge $global_clock) out |-> (a && b)
    );

    // If a is LOW, out must be LOW.
    check_a_low_forces_out_low: assert property (
        @(posedge $global_clock) !a |-> !out
    );

    // If b is LOW, out must be LOW.
    check_b_low_forces_out_low: assert property (
        @(posedge $global_clock) !b |-> !out
    );

    // If both inputs are HIGH, out must be HIGH.
    check_inputs_high_force_out_high: assert property (
        @(posedge $global_clock) (a && b) |-> out
    );
endmodule