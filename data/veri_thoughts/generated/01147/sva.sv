module top_module_sva (
    input logic clk,
    input logic reset,      // Synchronous active-high reset
    input logic [7:0] d,
    input logic [7:0] q,
    input logic [7:0] anyedge_or_d
);

    ///// dff_module (negedge clock) /////
    // When not in reset now and previously, q equals prior-cycle d at each negedge.
    dff_loads_d_on_negedge: assert property (
        @(negedge clk) disable iff (reset) (!$past(reset)) |-> (q == $past(d))
    );

    // If reset was asserted on the previous negedge, q must now be 0.
    dff_prev_reset_drives_zero: assert property (
        @(negedge clk) $past(reset) |-> (q == 8'h00)
    );

    // If reset is asserted on this negedge, q will be 0 by the next negedge.
    dff_reset_now_zero_next: assert property (
        @(negedge clk) reset |=> (q == 8'h00)
    );

    ///// anyedge_module + or_gate_module observed at posedge /////
    // OR output equals (q ^ d) OR (q toggled between the last two posedges).
    or_exact_decomposition: assert property (
        @(posedge clk) disable iff (reset) anyedge_or_d == ((q ^ d) | ($past(q) ^ $past(q,2)))
    );

    // OR output must include all 1s from (q ^ d).
    or_includes_q_xor_d: assert property (
        @(posedge clk) disable iff (reset) (((q ^ d) & ~anyedge_or_d) == 8'h00)
    );

    // OR output must include bits that toggled in q between the last two posedges.
    or_includes_prev_q_toggle: assert property (
        @(posedge clk) disable iff (reset) ((($past(q) ^ $past(q,2)) & ~anyedge_or_d) == 8'h00)
    );

    // If (q ^ d) is zero, OR output equals the previous-cycle anyedge term.
    or_reduces_to_prev_anyedge_when_qeqd: assert property (
        @(posedge clk) disable iff (reset) ((q ^ d) == 8'h00) |-> (anyedge_or_d == ($past(q) ^ $past(q,2)))
    );

    // If neither source contributes (q==d and no prior q toggle), OR output is zero.
    or_zero_when_no_sources: assert property (
        @(posedge clk) disable iff (reset) ((q == d) && ($past(q) == $past(q,2))) |-> (anyedge_or_d == 8'h00)
    );

    // After a posedge with reset asserted, next posedge OR output equals (q ^ d) (anyedge term cleared).
    or_after_reset_reduces_to_q_xor_d: assert property (
        @(posedge clk) reset |=> (anyedge_or_d == (q ^ d))
    );

endmodule