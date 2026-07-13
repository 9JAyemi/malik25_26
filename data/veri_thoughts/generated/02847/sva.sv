module top_module_sva (
    input logic clk,
    input logic [7:0] d,
    input logic [7:0] q
);
    ///// Timing and data propagation /////
    // At each negedge, q equals d from two negedges earlier (2-cycle delay at sample time).
    q_matches_past_d2: assert property (
        @(negedge clk) q == $past(d, 2)
    );

    // If d two cycles ago equals d three cycles ago, then q is unchanged since last negedge.
    q_stable_when_d_unchanged_two_cycles_ago: assert property (
        @(negedge clk) ($past(d,2) == $past(d,3)) |-> (q == $past(q))
    );

    // If d two cycles ago differs from three cycles ago, then q changed at this negedge.
    q_changes_when_d_changed_two_cycles_ago: assert property (
        @(negedge clk) ($past(d,2) != $past(d,3)) |-> (q != $past(q))
    );

    ///// Bit-level edge correspondence (per bit) /////
    genvar i;
    for (i = 0; i < 8; i++) begin : gen_bit_edges
        // A rising edge on d[i] appears as a rising edge on q[i] two negedges later.
        q_bit_rise_after_two_negedges: assert property (
            @(negedge clk) $rose(d[i]) |=> ##2 $rose(q[i])
        );
        // A falling edge on d[i] appears as a falling edge on q[i] two negedges later.
        q_bit_fall_after_two_negedges: assert property (
            @(negedge clk) $fell(d[i]) |=> ##2 $fell(q[i])
        );
        // If d[i] is unchanged across the window (k-3 to k-2), q[i] is unchanged (k-1 to k).
        q_bit_stable_when_d_past_stable: assert property (
            @(negedge clk) ($past(d[i],2) == $past(d[i],3)) |-> (q[i] == $past(q[i]))
        );
        // If d[i] changed across the window (k-3 to k-2), q[i] changes (k-1 to k).
        q_bit_changes_when_d_past_changed: assert property (
            @(negedge clk) ($past(d[i],2) != $past(d[i],3)) |-> (q[i] != $past(q[i]))
        );
    end
endmodule