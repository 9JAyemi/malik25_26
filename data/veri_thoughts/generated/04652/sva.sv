module dual_edge_triggered_ff_sva (
    input logic clk,
    input logic data,
    input logic q,
    input logic q_bar
);

    // q matches the data sampled on the prior rising edge after startup settles.
    check_q_tracks_prior_data: assert property (
        @(posedge clk) (!$initstate && !$past($initstate)) |-> (q === $past(data))
    );

    // q_bar matches the inverted data sampled on the prior rising edge after startup settles.
    check_qbar_tracks_prior_data_inv: assert property (
        @(posedge clk) (!$initstate && !$past($initstate)) |-> (q_bar === ~$past(data))
    );

    // q and q_bar are complementary after startup settles.
    check_outputs_complementary: assert property (
        @(posedge clk) (!$initstate && !$past($initstate)) |-> (q_bar === ~q)
    );

    // Stable input data keeps q stable on the following clock.
    check_q_stable_when_data_stable: assert property (
        @(posedge clk) ((!$initstate && !$past($initstate)) && (data === $past(data))) |=> (q === $past(q))
    );

    // Stable input data keeps q_bar stable on the following clock.
    check_qbar_stable_when_data_stable: assert property (
        @(posedge clk) ((!$initstate && !$past($initstate)) && (data === $past(data))) |=> (q_bar === $past(q_bar))
    );

endmodule