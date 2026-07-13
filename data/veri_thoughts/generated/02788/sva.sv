module top_module_sva (
    input logic clk,
    input logic slowena,
    input logic reset,
    input logic select,
    input logic a,
    input logic b,
    input logic out,
    input logic [3:0] count,
    input logic xor_out
);
    // Clock: clk. Reset: reset (active-high async in RTL). Mixed sequential/combinational logic.

    ///// Reset behavior /////
    // During reset, counter is 0.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 4'h0)
    );
    // During reset, out is 0.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |-> (out == 1'b0)
    );

    ///// XOR gate /////
    // xor_out equals a ^ b.
    check_xor_gate: assert property (
        @(posedge clk) disable iff (reset) xor_out == (a ^ b)
    );

    ///// Counter update rules /////
    // If previous cycle had slowena=1 (and not in reset), counter holds.
    check_count_hold_on_slowena: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) && $past(slowena) |-> (count == $past(count))
    );
    // If previous cycle had slowena=0 (and not in reset), counter increments by 1 (mod 16).
    check_count_inc_on_no_slowena: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) && !$past(slowena) |-> (count == ($past(count) + 4'd1))
    );
    // When incrementing from 15, counter wraps to 0.
    check_count_wrap_from_15: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) && !$past(slowena) && ($past(count) == 4'hF) |-> (count == 4'h0)
    );
    // Across cycles without reset, counter changes only by 0 or +1.
    check_count_step_0_or_1: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> ((count == $past(count)) || (count == ($past(count) + 4'd1)))
    );

    ///// Output selection /////
    // Out reflects previous-cycle mux: select ? xor_out : count[3].
    check_out_mux_function: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (out == ($past(select) ? $past(xor_out) : $past(count[3])))
    );
    // If XOR path was selected previously, out matches previous a ^ b.
    check_out_matches_xor_inputs: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) && $past(select) |-> (out == ($past(a) ^ $past(b)))
    );
    // If COUNT[3] path was selected previously, out matches previous count[3].
    check_out_matches_count_msb_path: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) && !$past(select) |-> (out == $past(count[3]))
    );
endmodule