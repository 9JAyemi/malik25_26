module axis_infrastructure_v1_1_clock_synchronizer_sva #(
    parameter integer C_NUM_STAGES = 4
) (
    input logic clk,
    input logic synch_in,
    input logic synch_out
);

    localparam integer P_SYNCH_D_WIDTH = (C_NUM_STAGES > 0) ? C_NUM_STAGES : 1;

    generate
        if (C_NUM_STAGES > 0) begin : gen_synchronizer_checks
            // synch_out is the delayed version of synch_in by C_NUM_STAGES clocks.
            check_output_delay: assert property (
                @(posedge clk) disable iff ($initstate)
                synch_out == $past(synch_in, C_NUM_STAGES)
            );

            // A rising input appears on the output C_NUM_STAGES clocks later.
            check_rise_propagates: assert property (
                @(posedge clk) disable iff ($initstate)
                $rose(synch_in) |-> ##C_NUM_STAGES $rose(synch_out)
            );

            // A falling input appears on the output C_NUM_STAGES clocks later.
            check_fall_propagates: assert property (
                @(posedge clk) disable iff ($initstate)
                $fell(synch_in) |-> ##C_NUM_STAGES $fell(synch_out)
            );

            // A stable input keeps the output stable C_NUM_STAGES clocks later.
            check_stable_propagates: assert property (
                @(posedge clk) disable iff ($initstate)
                $stable(synch_in) |-> ##C_NUM_STAGES $stable(synch_out)
            );
        end
        else begin : gen_no_synchronizer_checks
            // When no stages are present, the output follows the input immediately.
            check_no_stage_passthrough: assert property (
                @(posedge clk) disable iff ($initstate)
                synch_out == synch_in
            );
        end
    endgenerate

endmodule