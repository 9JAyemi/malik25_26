module axis_infrastructure_v1_1_clock_synchronizer_sva (
    input logic clk,
    input logic synch_in,
    input logic synch_out
);

// synch_out is the registered input value from C_NUM_STAGES clocks ago.
    check_sync_pipeline: assert property (
        @(posedge clk) 1'b1 |-> ##(C_NUM_STAGES) (synch_out == $past(synch_in, C_NUM_STAGES))
    );

// With C_NUM_STAGES==0, synch_out is a direct copy of synch_in.
    check_no_pipeline_passthrough: assert property (
        @(posedge clk) (C_NUM_STAGES == 0) |-> (synch_out == synch_in)
    );

// With C_NUM_STAGES==1, synch_out is registered synch_in from the previous clock.
    check_one_stage_pipeline: assert property (
        @(posedge clk) (C_NUM_STAGES == 1) |-> ##1 (synch_out == $past(synch_in))
    );

// With C_NUM_STAGES==2, synch_out is registered synch_in from two previous clocks.
    check_two_stage_pipeline: assert property (
        @(posedge clk) (C_NUM_STAGES == 2) |-> ##2 (synch_out == $past(synch_in, 2))
    );

// With C_NUM_STAGES==3, synch_out is registered synch_in from three previous clocks.
    check_three_stage_pipeline: assert property (
        @(posedge clk) (C_NUM_STAGES == 3) |-> ##3 (synch_out == $past(synch_in, 3))
    );

// With C_NUM_STAGES==4, synch_out is registered synch_in from four previous clocks.
    check_four_stage_pipeline: assert property (
        @(posedge clk) (C_NUM_STAGES == 4) |-> ##4 (synch_out == $past(synch_in, 4))
    );

endmodule
