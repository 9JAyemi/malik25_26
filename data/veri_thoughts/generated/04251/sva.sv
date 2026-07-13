module ddr3_s4_uniphy_example_sim_ddr3_s4_uniphy_example_sim_e0_if0_p0_hr_to_fr_sva (
    input logic clk,
    input logic d_h0,
    input logic d_h1,
    input logic d_l0,
    input logic d_l1,
    input logic q0,
    input logic q1
);

    // q0 shows the prior high-path sample at each sampled posedge.
    check_q0_h_path_sample: assert property (
        @(posedge clk)
        !$isunknown($past(d_h0)) |-> (q0 === $past(d_h0))
    );

    // q1 shows the prior high-path sample at each sampled posedge.
    check_q1_h_path_sample: assert property (
        @(posedge clk)
        !$isunknown($past(d_h1)) |-> (q1 === $past(d_h1))
    );

    // q0 shows the prior low-path sample at each sampled negedge.
    check_q0_l_path_sample: assert property (
        @(negedge clk)
        !$isunknown($past(d_l0, 2, 1'b1, @(posedge clk))) |-> (q0 === $past(d_l0, 2, 1'b1, @(posedge clk)))
    );

    // q1 shows the prior low-path sample at each sampled negedge.
    check_q1_l_path_sample: assert property (
        @(negedge clk)
        !$isunknown($past(d_l1, 2, 1'b1, @(posedge clk))) |-> (q1 === $past(d_l1, 2, 1'b1, @(posedge clk)))
    );

    // Equal high-path samples produce equal outputs at posedge.
    check_equal_h_samples_equal_outputs: assert property (
        @(posedge clk)
        !$isunknown($past(d_h0)) &&
        !$isunknown($past(d_h1)) &&
        ($past(d_h0) == $past(d_h1)) |-> (q0 === q1)
    );

    // Different high-path samples produce different outputs at posedge.
    check_distinct_h_samples_distinct_outputs: assert property (
        @(posedge clk)
        !$isunknown($past(d_h0)) &&
        !$isunknown($past(d_h1)) &&
        ($past(d_h0) != $past(d_h1)) |-> (q0 != q1)
    );

    // Equal low-path samples produce equal outputs at negedge.
    check_equal_l_samples_equal_outputs: assert property (
        @(negedge clk)
        !$isunknown($past(d_l0, 2, 1'b1, @(posedge clk))) &&
        !$isunknown($past(d_l1, 2, 1'b1, @(posedge clk))) &&
        ($past(d_l0, 2, 1'b1, @(posedge clk)) == $past(d_l1, 2, 1'b1, @(posedge clk))) |-> (q0 === q1)
    );

    // Different low-path samples produce different outputs at negedge.
    check_distinct_l_samples_distinct_outputs: assert property (
        @(negedge clk)
        !$isunknown($past(d_l0, 2, 1'b1, @(posedge clk))) &&
        !$isunknown($past(d_l1, 2, 1'b1, @(posedge clk))) &&
        ($past(d_l0, 2, 1'b1, @(posedge clk)) != $past(d_l1, 2, 1'b1, @(posedge clk))) |-> (q0 != q1)
    );

endmodule