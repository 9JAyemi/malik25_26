module chatgpt_generate_edge_detect_sva (
    input logic clk,
    input logic rst_n,
    input logic a,
    input logic rise,
    input logic down,
    input logic a_dly,
    input logic a_dly_dly,
    input logic a_dly_dly_dly
);

    // Reset forces the delay pipeline low.
    check_reset_pipeline_low: assert property (
        @(posedge clk) disable iff ($initstate)
        !rst_n |-> (a_dly == 1'b0) && (a_dly_dly == 1'b0) && (a_dly_dly_dly == 1'b0)
    );

    // Reset forces both outputs low.
    check_reset_outputs_low: assert property (
        @(posedge clk) disable iff ($initstate)
        !rst_n |-> (rise == 1'b0) && (down == 1'b0)
    );

    // State and outputs remain low immediately after a reset cycle.
    check_post_reset_state_low: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate)
        !$past(rst_n) |-> (a_dly == 1'b0) && (a_dly_dly == 1'b0) && (a_dly_dly_dly == 1'b0) &&
                          (rise == 1'b0) && (down == 1'b0)
    );

    // First delay stage captures input a.
    check_a_dly_captures_a: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate)
        $past(rst_n) |-> (a_dly == $past(a))
    );

    // Second delay stage captures the first delay stage.
    check_a_dly_dly_captures_a_dly: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate)
        $past(rst_n) |-> (a_dly_dly == $past(a_dly))
    );

    // Third delay stage captures the second delay stage.
    check_a_dly_dly_dly_captures_a_dly_dly: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate)
        $past(rst_n) |-> (a_dly_dly_dly == $past(a_dly_dly))
    );

    // Rise output matches the registered 0,1,1 detect pattern.
    check_rise_decode: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate)
        $past(rst_n) |-> (rise == (($past(a_dly_dly_dly) == 1'b0) &&
                                   ($past(a_dly_dly) == 1'b1) &&
                                   ($past(a_dly) == 1'b1)))
    );

    // Down output matches the registered 1,1,0 detect pattern.
    check_down_decode: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate)
        $past(rst_n) |-> (down == (($past(a_dly_dly_dly) == 1'b1) &&
                                   ($past(a_dly_dly) == 1'b1) &&
                                   ($past(a_dly) == 1'b0)))
    );

    // Rise and down are never asserted together.
    check_outputs_mutex: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate)
        !((rise == 1'b1) && (down == 1'b1))
    );

    // Rise is a single-cycle pulse.
    check_rise_single_cycle: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate)
        (rise == 1'b1) |=> (rise == 1'b0)
    );

    // Down is a single-cycle pulse.
    check_down_single_cycle: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate)
        (down == 1'b1) |=> (down == 1'b0)
    );

endmodule