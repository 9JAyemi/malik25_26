module top_module_sva (
    input logic [15:0] in0,
    input logic [15:0] in1,
    input logic        CTRL,
    input logic        CLK,
    input logic [15:0] OUT_ADDSUB,
    input logic [15:0] OUT_DIFF
);

    // Assertions are sampled on CLK; the RTL has no reset.
    
    // OUT_ADDSUB selects the adder result when CTRL is low.
    check_out_addsub_select_add: assert property (
        @(posedge CLK) (!CTRL) |-> (OUT_ADDSUB == (in0 + in1))
    );

    // OUT_ADDSUB selects the subtractor result when CTRL is high.
    check_out_addsub_select_sub: assert property (
        @(posedge CLK) CTRL |-> (OUT_ADDSUB == (in0 - in1))
    );

    // OUT_DIFF uses add_out - sub_out when add_out is larger.
    check_out_diff_add_greater_branch: assert property (
        @(posedge CLK) ((in0 + in1) > (in0 - in1)) |-> (OUT_DIFF == ((in0 + in1) - (in0 - in1)))
    );

    // OUT_DIFF uses sub_out - add_out when sub_out is larger or equal.
    check_out_diff_sub_greater_equal_branch: assert property (
        @(posedge CLK) ((in0 + in1) <= (in0 - in1)) |-> (OUT_DIFF == ((in0 - in1) - (in0 + in1)))
    );

    // Zero on in1 makes the absolute difference zero.
    check_zero_in1_zero_diff: assert property (
        @(posedge CLK) (in1 == 16'h0000) |-> (OUT_DIFF == 16'h0000)
    );

    // Zero on in1 makes OUT_ADDSUB pass through in0.
    check_zero_in1_addsub_passthrough: assert property (
        @(posedge CLK) (in1 == 16'h0000) |-> (OUT_ADDSUB == in0)
    );

    // Equal inputs make the subtractor-selected output zero.
    check_equal_inputs_sub_zero: assert property (
        @(posedge CLK) (CTRL && (in0 == in1)) |-> (OUT_ADDSUB == 16'h0000)
    );

    // Equal inputs make OUT_DIFF equal the adder result.
    check_equal_inputs_diff_matches_sum: assert property (
        @(posedge CLK) (in0 == in1) |-> (OUT_DIFF == (in0 + in1))
    );

endmodule