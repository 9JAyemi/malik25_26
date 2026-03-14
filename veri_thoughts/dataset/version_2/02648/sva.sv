module and_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic out
);
    // Analysis: no clock/reset in RTL; pure combinational; out = (a & b & c) | c = c.

    // out must always equal c.
    check_out_equals_c: assert property (
        @(posedge clk) disable iff (1'b0) out == c
    );

    // When c is 1, out must be 1.
    check_out_high_when_c_high: assert property (
        @(posedge clk) disable iff (1'b0) (c == 1'b1) |-> (out == 1'b1)
    );

    // When c is 0, out must be 0.
    check_out_low_when_c_low: assert property (
        @(posedge clk) disable iff (1'b0) (c == 1'b0) |-> (out == 1'b0)
    );

    // A rising edge on c must produce a rising edge on out in the same cycle.
    check_out_rise_follows_c_rise: assert property (
        @(posedge clk) disable iff (1'b0) $rose(c) |-> $rose(out)
    );

    // A falling edge on c must produce a falling edge on out in the same cycle.
    check_out_fall_follows_c_fall: assert property (
        @(posedge clk) disable iff (1'b0) $fell(c) |-> $fell(out)
    );

    // out cannot rise unless c rises.
    check_no_spurious_out_rise: assert property (
        @(posedge clk) disable iff (1'b0) $rose(out) |-> $rose(c)
    );

    // out cannot fall unless c falls.
    check_no_spurious_out_fall: assert property (
        @(posedge clk) disable iff (1'b0) $fell(out) |-> $fell(c)
    );

    // If c is stable across cycles, out must also be stable.
    check_out_stable_when_c_stable: assert property (
        @(posedge clk) disable iff (1'b0) $stable(c) |-> $stable(out)
    );

    // Toggling a while c is stable must not change out.
    check_a_toggle_no_effect_when_c_stable: assert property (
        @(posedge clk) disable iff (1'b0) ($changed(a) && $stable(c)) |-> $stable(out)
    );

    // Toggling b while c is stable must not change out.
    check_b_toggle_no_effect_when_c_stable: assert property (
        @(posedge clk) disable iff (1'b0) ($changed(b) && $stable(c)) |-> $stable(out)
    );
endmodule