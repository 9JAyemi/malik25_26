module top_module_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [7:0] out_edge,
    input logic out_not,
    input logic [7:0] out_func
);
    // Clock: clk; no explicit reset in RTL.
    // Mixed logic: edge_detector is sequential; not_gate and functional_module are combinational.
    // Behavior: out_not = in[0]^1; out_edge = in & ~past(in); out_func = out_edge & {8{out_not}}.

    ///// not_gate /////
    // out_not is the inversion of in[0].
    check_not_gate_inversion: assert property (
        @(posedge clk) disable iff ($initstate) out_not == (in[0] ^ 1'b1)
    );
    // Rising in[0] implies falling out_not.
    check_not_falls_on_in0_rise: assert property (
        @(posedge clk) disable iff ($initstate) $rose(in[0]) |-> $fell(out_not)
    );
    // Falling in[0] implies rising out_not.
    check_not_rises_on_in0_fall: assert property (
        @(posedge clk) disable iff ($initstate) $fell(in[0]) |-> $rose(out_not)
    );

    ///// edge_detector /////
    // out_edge equals current in AND NOT previous in (per-bit rising edge).
    check_edge_exact_definition: assert property (
        @(posedge clk) disable iff ($initstate) out_edge == (in & ~ $past(in))
    );
    // out_edge can only assert where in is 1 (subset of in).
    check_edge_subset_of_in: assert property (
        @(posedge clk) disable iff ($initstate) (out_edge & ~in) == 8'b0
    );
    // If previous in bit was 1, current out_edge bit must be 0 (no pulse without a rise).
    check_edge_zero_if_prev_one: assert property (
        @(posedge clk) disable iff ($initstate) (( $past(in) & out_edge ) == 8'b0)
    );
    // No bit of out_edge can be 1 in two consecutive cycles.
    check_edge_no_consecutive_pulses: assert property (
        @(posedge clk) disable iff ($initstate) (out_edge & $past(out_edge)) == 8'b0
    );

    ///// functional_module /////
    // out_func equals out_edge AND replicated out_not.
    check_func_masking_exact: assert property (
        @(posedge clk) disable iff ($initstate) out_func == (out_edge & {8{out_not}})
    );
    // When out_not is 0, out_func must be all zeros.
    check_func_zero_when_blocked: assert property (
        @(posedge clk) disable iff ($initstate) (!out_not) |-> (out_func == 8'b0)
    );
    // When out_not is 1, out_func must equal out_edge.
    check_func_pass_through: assert property (
        @(posedge clk) disable iff ($initstate) (out_not) |-> (out_func == out_edge)
    );
    // out_func can only assert where out_edge is 1 (subset of out_edge).
    check_func_subset_of_edge: assert property (
        @(posedge clk) disable iff ($initstate) (out_func & ~out_edge) == 8'b0
    );

endmodule