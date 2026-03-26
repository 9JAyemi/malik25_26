module synchronizer_sva #(
    parameter DW = 1
) (
    input logic [DW-1:0] out,
    input logic [DW-1:0] in,
    input logic          clk,
    input logic          reset,
    input logic [DW-1:0] sync_reg0
);

    // A sampled reset clears both synchronizer stages by the next clock.
    check_reset_clears_pipeline: assert property (
        @(posedge clk)
        reset |=> ((sync_reg0 == {(DW){1'b0}}) && (out == {(DW){1'b0}}))
    );

    // On the first clock after reset deasserts, both stages are still zero.
    check_first_cycle_after_reset_release_zero: assert property (
        @(posedge clk)
        reset ##1 !reset |-> ((sync_reg0 == {(DW){1'b0}}) && (out == {(DW){1'b0}}))
    );

    // On the second clock after reset deasserts, out is still zero.
    check_second_cycle_after_reset_release_out_zero: assert property (
        @(posedge clk)
        reset ##1 !reset ##1 !reset |-> (out == {(DW){1'b0}})
    );

    // In reset-free operation, stage0 is either the prior input or zero from async reset.
    check_stage0_tracks_input_or_zero: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((sync_reg0 == $past(in)) || (sync_reg0 == {(DW){1'b0}}))
    );

    // In reset-free operation, out is either the prior stage0 value or zero from async reset.
    check_out_tracks_stage0_or_zero: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((out == $past(sync_reg0)) || (out == {(DW){1'b0}}))
    );

    // After two reset-free clocks, out is either the two-cycle delayed input or zero from reset.
    check_out_is_delayed_input_or_zero: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 ##1 1'b1 |=> ((out == $past(in,2)) || (out == {(DW){1'b0}}))
    );

endmodule