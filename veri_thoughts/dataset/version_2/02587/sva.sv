module dual_edge_ff_sva (
    input logic clk,
    input logic data,
    input logic Q,
    input logic Q_bar,
    input logic Q_temp
);
    // Q equals data sampled on the previous posedge.
    check_q_matches_prev_posedge_data: assert property (
        @(posedge clk) 1 |=> (Q == $past(data))
    );

    // Q_bar equals complement of data sampled on the previous posedge.
    check_qbar_matches_prev_posedge_data_complement: assert property (
        @(posedge clk) 1 |=> (Q_bar == ~ $past(data))
    );

    // Outputs are always complements at posedge sampling.
    check_outputs_are_complements_posedge: assert property (
        @(posedge clk) 1 |=> (Q_bar == ~Q)
    );

    // At each posedge sample, Q equals Q_temp (both represent last-posedge data).
    check_q_equals_qtemp_at_posedge: assert property (
        @(posedge clk) 1 |=> (Q == Q_temp)
    );

    // At each posedge sample, Q_bar equals complement of Q_temp.
    check_qbar_equals_not_qtemp_at_posedge: assert property (
        @(posedge clk) 1 |=> (Q_bar == ~Q_temp)
    );

    // Q and Q_bar change together between consecutive posedges.
    check_outputs_change_together_posedge: assert property (
        @(posedge clk) 1 |=> ($changed(Q) == $changed(Q_bar))
    );

    // At negedge-to-negedge, Q equals the previously sampled Q_temp.
    check_q_follows_qtemp_negedge: assert property (
        @(negedge clk) 1 |=> (Q == $past(Q_temp))
    );

    // At negedge-to-negedge, Q_bar equals complement of the previously sampled Q_temp.
    check_qbar_follows_not_qtemp_negedge: assert property (
        @(negedge clk) 1 |=> (Q_bar == ~ $past(Q_temp))
    );

    // Outputs are always complements at negedge sampling.
    check_outputs_are_complements_negedge: assert property (
        @(negedge clk) 1 |=> (Q_bar == ~Q)
    );

    // If data changes between two consecutive posedges, both outputs change by the next posedge.
    check_output_change_reflects_data_change: assert property (
        @(posedge clk) 1 |=> 1 |=> (($past(data) != $past(data,2)) |-> ($changed(Q) && $changed(Q_bar)))
    );
endmodule