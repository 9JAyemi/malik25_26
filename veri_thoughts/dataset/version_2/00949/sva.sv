module shift_register_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);
    ///// Shift behavior per stage /////
    // Stage0 captures data_in[0] one cycle later.
    check_stage0_captures_data_in0: assert property (
        @(posedge clk) 1'b1 |=> (data_out[0] == $past(data_in[0]))
    );
    // Stage1 captures previous stage0 value.
    check_stage1_follows_prev_stage: assert property (
        @(posedge clk) 1'b1 |=> (data_out[1] == $past(data_out[0]))
    );
    // Stage2 captures previous stage1 value.
    check_stage2_follows_prev_stage: assert property (
        @(posedge clk) 1'b1 |=> (data_out[2] == $past(data_out[1]))
    );
    // Stage3 captures previous stage2 value.
    check_stage3_follows_prev_stage: assert property (
        @(posedge clk) 1'b1 |=> (data_out[3] == $past(data_out[2]))
    );

    ///// Vector-level shift relation /////
    // Full vector equals previous vector left-shifted with prior data_in[0] inserted at bit0.
    check_vector_shift: assert property (
        @(posedge clk) 1'b1 |=> (data_out == { $past(data_out[2]), $past(data_out[1]), $past(data_out[0]), $past(data_in[0]) })
    );

    ///// Depth to input relation /////
    // Stage1 equals data_in[0] from two cycles earlier.
    check_stage1_matches_input_2cycle: assert property (
        @(posedge clk) 1'b1 |=> ##2 (data_out[1] == $past(data_in[0], 2))
    );
    // Stage2 equals data_in[0] from three cycles earlier.
    check_stage2_matches_input_3cycle: assert property (
        @(posedge clk) 1'b1 |=> ##3 (data_out[2] == $past(data_in[0], 3))
    );
    // Stage3 equals data_in[0] from four cycles earlier.
    check_stage3_matches_input_4cycle: assert property (
        @(posedge clk) 1'b1 |=> ##4 (data_out[3] == $past(data_in[0], 4))
    );

    ///// Cross-stage timing consistency /////
    // Stage2 equals stage0 from two cycles earlier.
    check_stage2_matches_stage0_2cycle: assert property (
        @(posedge clk) 1'b1 |=> ##2 (data_out[2] == $past(data_out[0], 2))
    );
    // Stage3 equals stage1 from two cycles earlier.
    check_stage3_matches_stage1_2cycle: assert property (
        @(posedge clk) 1'b1 |=> ##2 (data_out[3] == $past(data_out[1], 2))
    );
    // Stage3 equals stage0 from three cycles earlier.
    check_stage3_matches_stage0_3cycle: assert property (
        @(posedge clk) 1'b1 |=> ##3 (data_out[3] == $past(data_out[0], 3))
    );
endmodule