module top_module_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic reset,
    input logic out
);
    // Out must equal XOR of a and b on any input edge.
    check_out_equals_xor: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c or posedge reset or negedge reset)
        disable iff (reset) out == (a ^ b)
    );

    // When inputs are equal, out is 0.
    check_out_zero_when_inputs_equal: assert property (
        @(posedge a or negedge a or posedge b or negedge b)
        disable iff (reset) (a == b) |-> (out == 1'b0)
    );

    // When inputs differ, out is 1.
    check_out_one_when_inputs_differ: assert property (
        @(posedge a or negedge a or posedge b or negedge b)
        disable iff (reset) (a != b) |-> (out == 1'b1)
    );

    // Out is unaffected by c edges when a and b are stable.
    check_out_stable_on_c_edges: assert property (
        @(posedge c or negedge c)
        disable iff (reset) ($stable(a) && $stable(b)) |-> $stable(out)
    );

    // Out is unaffected by falling edge of reset when a and b are stable.
    check_out_stable_on_reset_fall: assert property (
        @(negedge reset)
        disable iff (reset) ($stable(a) && $stable(b)) |-> $stable(out)
    );

    // If out changes on c/reset edges, then a or b must have changed.
    check_out_change_only_due_to_ab_on_c_or_reset: assert property (
        @(posedge c or negedge c or negedge reset)
        disable iff (reset) $changed(out) |-> ($changed(a) || $changed(b))
    );

    // If both a and b toggle in the same cycle, out remains stable.
    check_out_stable_when_both_ab_toggle: assert property (
        @(posedge a or negedge a or posedge b or negedge b)
        disable iff (reset) ($changed(a) && $changed(b)) |-> $stable(out)
    );

    // If exactly one of a or b toggles, out must toggle.
    check_out_toggles_when_one_of_ab_toggles: assert property (
        @(posedge a or negedge a or posedge b or negedge b)
        disable iff (reset) ($changed(a) ^ $changed(b)) |-> $changed(out)
    );
endmodule