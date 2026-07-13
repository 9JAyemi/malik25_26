module dff_chain_sva (
    input logic        clk,
    input logic        reset,
    input logic [7:0]  d,
    input logic [7:0]  q,
    input logic [7:0]  q1,
    input logic [7:0]  q2,
    input logic [7:0]  q3
);

    // A sampled low reset leaves every stage cleared by the next clock.
    check_reset_clears_all_stages: assert property (
        @(posedge clk)
        !reset |=> ((q1 == 8'h00) && (q2 == 8'h00) && (q3 == 8'h00) && (q == 8'h00))
    );

    // On the first clock after reset deassertion, all stages are still zero.
    check_release_all_stages_zero: assert property (
        @(posedge clk) disable iff (!reset)
        $rose(reset) |-> ((q1 == 8'h00) && (q2 == 8'h00) && (q3 == 8'h00) && (q == 8'h00))
    );

    // One clock after reset deassertion, the tail stages remain zero.
    check_release_second_clock_zero_tail: assert property (
        @(posedge clk) disable iff (!reset)
        $rose(reset) |=> ((q2 == 8'h00) && (q3 == 8'h00) && (q == 8'h00))
    );

    // Two clocks after reset deassertion, q3 and q remain zero.
    check_release_third_clock_zero_tail: assert property (
        @(posedge clk) disable iff (!reset)
        $rose(reset) |=> ##1 ((q3 == 8'h00) && (q == 8'h00))
    );

    // Three clocks after reset deassertion, q is still zero.
    check_release_fourth_clock_q_zero: assert property (
        @(posedge clk) disable iff (!reset)
        $rose(reset) |=> ##2 (q == 8'h00)
    );

    // A zero input sample reaches q1 on the next clock.
    check_zero_input_captured_into_q1: assert property (
        @(posedge clk) disable iff (!reset)
        (d == 8'h00) |=> (q1 == 8'h00)
    );

    // A zero in q1 shifts into q2 on the next clock.
    check_zero_q1_shifts_into_q2: assert property (
        @(posedge clk) disable iff (!reset)
        (q1 == 8'h00) |=> (q2 == 8'h00)
    );

    // A zero in q2 shifts into q3 on the next clock.
    check_zero_q2_shifts_into_q3: assert property (
        @(posedge clk) disable iff (!reset)
        (q2 == 8'h00) |=> (q3 == 8'h00)
    );

    // A zero in q3 shifts into q on the next clock.
    check_zero_q3_shifts_into_q: assert property (
        @(posedge clk) disable iff (!reset)
        (q3 == 8'h00) |=> (q == 8'h00)
    );

    // Four consecutive zero input samples force a zero at the output.
    check_four_zero_inputs_produce_zero_q: assert property (
        @(posedge clk) disable iff (!reset)
        ((d == 8'h00) ##1 (d == 8'h00) ##1 (d == 8'h00) ##1 (d == 8'h00)) |=> (q == 8'h00)
    );

endmodule

bind dff_chain dff_chain_sva dff_chain_sva_i (
    .clk(clk),
    .reset(reset),
    .d(d),
    .q(q),
    .q1(q1),
    .q2(q2),
    .q3(q3)
);