module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic f
);

    // f is the XOR of a and b.
    check_f_matches_xor: assert property (
        @(posedge clk) f == (a ^ b)
    );

    // When a and b are equal, f is low.
    check_equal_inputs_drive_low: assert property (
        @(posedge clk) (a == b) |-> (f == 1'b0)
    );

    // When a and b differ, f is high.
    check_different_inputs_drive_high: assert property (
        @(posedge clk) (a != b) |-> (f == 1'b1)
    );

    // f is independent of the previous cycle's a and b values.
    check_f_is_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> $stable(f)
    );

    // f toggles when a and b differ in the previous cycle.
    check_f_toggles_when_inputs_differ: assert property (
        @(posedge clk) ($past(a) != $past(b)) |-> (f != $past(f))
    );

    // f holds when a and b are equal in the previous cycle.
    check_f_holds_when_inputs_equal: assert property (
        @(posedge clk) ($past(a) == $past(b)) |-> (f == $past(f))
    );

endmodule