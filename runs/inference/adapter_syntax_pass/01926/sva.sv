module axis_infrastructure_v1_1_clock_synchronizer_sva #(
    parameter integer C_NUM_STAGES = 4
) (
    input logic clk,
    input logic synch_in,
    input logic synch_out
);

    localparam integer P_SYNCH_D_WIDTH = (C_NUM_STAGES > 0) ? C_NUM_STAGES : 1;

    generate
        if (C_NUM_STAGES > 0) begin : gen_synchronizer
            // synch_out is the delayed input from C_NUM_STAGES clock edges later.
            check_output_matches_input_after_stages: assert property (
                @(posedge clk) 1'b1 |-> ##C_NUM_STAGES (synch_out == $past(synch_in, C_NUM_STAGES))
            );

            // synch_out is always the same value on consecutive sampled cycles.
            check_output_is_stable: assert property (
                @(posedge clk) 1'b1 |-> ##1 (synch_out == $past(synch_out))
            );

            // synch_out is never high-impedance.
            check_output_is_not_highz: assert property (
                @(posedge clk) 1'b1 |-> ##1 (synch_out !== 1'bz)
            );
        end
        else begin : gen_no_synchronizer
            // When no stages are used, synch_out passes through synch_in immediately.
            check_passthrough_when_no_stages: assert property (
                @(posedge clk) 1'b1 |-> ##1 (synch_out == $past(synch_in))
            );
        end
    endgenerate

endmodule