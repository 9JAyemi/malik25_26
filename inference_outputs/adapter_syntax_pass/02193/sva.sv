module top_module_sva (
    input logic clk,
    input logic [7:0] d,
    input logic [7:0] q
);

    // q equals d sampled on the previous falling edge.
    check_q_matches_prev_d: assert property (
        @(negedge clk) 1'b1 |=> (q == $past(d))
    );

    // A rising edge on d is captured into q on the next falling edge.
    check_rise_d_captured: assert property (
        @(negedge clk) $rose(d) |=> (q == $past(d))
    );

    // A falling edge on d is captured into q on the next falling edge.
    check_fall_d_captured: assert property (
        @(negedge clk) $fell(d) |=> (q == $past(d))
    );

    // A stable d across cycles keeps q stable on the next falling edge.
    check_stable_d_keeps_q_stable: assert property (
        @(negedge clk) $stable(d) |=> $stable(q)
    );

    // A change on d across cycles causes a change on q on the next falling edge.
    check_change_d_causes_change_q: assert property (
        @(negedge clk) $changed(d) |=> $changed(q)
    );

endmodule