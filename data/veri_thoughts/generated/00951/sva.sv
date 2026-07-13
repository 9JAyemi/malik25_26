module and_gate_sva (
    input logic clk,   // External sampling clock (RTL has no clock/reset)
    input logic a,
    input logic b,
    input logic out
);
    // out must equal a & b every cycle.
    check_and_equivalence: assert property (
        @(posedge clk) out == (a & b)
    );

    // out HIGH only when both inputs are HIGH.
    check_out_high_implies_inputs_high: assert property (
        @(posedge clk) out |=> (a && b)
    );

    // If any input is LOW, out must be LOW.
    check_any_input_low_forces_out_low: assert property (
        @(posedge clk) (!a || !b) |=> (!out)
    );

    // If both inputs are HIGH, out must be HIGH.
    check_inputs_high_implies_out_high: assert property (
        @(posedge clk) (a && b) |=> out
    );

    // out can change only if at least one input changed.
    check_out_change_needs_input_change: assert property (
        @(posedge clk) $changed(out) |=> ($changed(a) || $changed(b))
    );

    // If both inputs are stable, out must be stable.
    check_stable_inputs_keep_out_stable: assert property (
        @(posedge clk) (!$changed(a) && !$changed(b)) |=> !$changed(out)
    );
endmodule