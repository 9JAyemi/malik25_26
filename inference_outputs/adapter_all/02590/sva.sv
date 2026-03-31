module d_flip_flop_mux_sva (
    input logic clk,
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic sel,
    input logic [7:0] q
);

    // q reflects the d input selected on the previous falling edge.
    check_q_matches_selected_input: assert property (
        @(negedge clk) 1'b1 |=> (q == $past(sel ? d2 : d1))
    );

    // A low sel selects d1 on the next falling edge.
    check_sel_low_selects_d1: assert property (
        @(negedge clk) !sel |=> (q == $past(d1))
    );

    // A high sel selects d2 on the next falling edge.
    check_sel_high_selects_d2: assert property (
        @(negedge clk) sel |=> (q == $past(d2))
    );

    // With stable d1 and d2, a low sel holds q at the next falling edge.
    check_stable_d1_keeps_q_when_sel_low: assert property (
        @(negedge clk) (!sel && $stable(d1) && $stable(d2)) |=> (q == $past(d1))
    );

    // With stable d1 and d2, a high sel holds q at the next falling edge.
    check_stable_d2_keeps_q_when_sel_high: assert property (
        @(negedge clk) (sel && $stable(d1) && $stable(d2)) |=> (q == $past(d2))
    );

    // With stable d1 and d2, a low sel does not change q on the next falling edge.
    check_stable_d1_no_change_when_sel_low: assert property (
        @(negedge clk) (!sel && $stable(d1) && $stable(d2)) |=> (q == $past(q))
    );

    // With stable d1 and d2, a high sel does not change q on the next falling edge.
    check_stable_d2_no_change_when_sel_high: assert property (
        @(negedge clk) (sel && $stable(d1) && $stable(d2)) |=> (q == $past(q))
    );

endmodule