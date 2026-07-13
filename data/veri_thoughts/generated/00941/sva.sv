module top_module_sva (
    input logic CLK,
    input logic [7:0] d_in,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    input logic [7:0] max,
    input logic [7:0] sum_out
);
    // module_1: out equals a+b+c+d (8-bit modulo)
    check_sum_out_is_sum: assert property (
        @(posedge CLK) sum_out == (a + b + c + d)
    );
    // module_2: out equals in
    check_max_equals_sum_out: assert property (
        @(posedge CLK) max == sum_out
    );
    // top_module: max equals a+b+c+d (composition correctness)
    check_max_matches_sum_expr: assert property (
        @(posedge CLK) max == (a + b + c + d)
    );
    // With a,b,c,d stable, sum_out must be stable (purely combinational)
    stable_inputs_imply_stable_sum_out: assert property (
        @(posedge CLK) $stable(a) && $stable(b) && $stable(c) && $stable(d) |-> $stable(sum_out)
    );
    // With a,b,c,d stable, max must be stable (purely combinational)
    stable_inputs_imply_stable_max: assert property (
        @(posedge CLK) $stable(a) && $stable(b) && $stable(c) && $stable(d) |-> $stable(max)
    );
    // Change only in a must change outputs
    change_a_only_changes_outputs: assert property (
        @(posedge CLK) $changed(a) && $stable(b) && $stable(c) && $stable(d) |-> $changed(sum_out) && $changed(max)
    );
    // Change only in b must change outputs
    change_b_only_changes_outputs: assert property (
        @(posedge CLK) $changed(b) && $stable(a) && $stable(c) && $stable(d) |-> $changed(sum_out) && $changed(max)
    );
    // Change only in c must change outputs
    change_c_only_changes_outputs: assert property (
        @(posedge CLK) $changed(c) && $stable(a) && $stable(b) && $stable(d) |-> $changed(sum_out) && $changed(max)
    );
    // Change only in d must change outputs
    change_d_only_changes_outputs: assert property (
        @(posedge CLK) $changed(d) && $stable(a) && $stable(b) && $stable(c) |-> $changed(sum_out) && $changed(max)
    );
    // Changes on unused d_in do not affect outputs when a,b,c,d are stable
    din_change_does_not_affect_outputs: assert property (
        @(posedge CLK) $changed(d_in) && $stable(a) && $stable(b) && $stable(c) && $stable(d) |-> $stable(sum_out) && $stable(max)
    );
    // If sum_out changes, max must change in the same cycle (pass-through)
    change_coherency_sum_out_to_max: assert property (
        @(posedge CLK) $changed(sum_out) |-> $changed(max)
    );
    // If max changes, sum_out must change in the same cycle (pass-through)
    change_coherency_max_to_sum_out: assert property (
        @(posedge CLK) $changed(max) |-> $changed(sum_out)
    );
    // All-zero inputs yield zero outputs
    zero_inputs_yield_zero_outputs: assert property (
        @(posedge CLK) (a == 8'h00 && b == 8'h00 && c == 8'h00 && d == 8'h00) |-> (sum_out == 8'h00 && max == 8'h00)
    );
endmodule