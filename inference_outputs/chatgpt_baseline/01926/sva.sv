module axis_infrastructure_v1_1_clock_synchronizer_sva #(
    parameter integer C_NUM_STAGES = 4
) (
    input logic clk,
    input logic synch_in,
    input logic synch_out
);
    // Output reflects either final stage or direct input based on C_NUM_STAGES.
    check_synch_out_mapping: assert property (
        @(posedge clk) synch_out == ((C_NUM_STAGES > 0) ? synch_d[C_NUM_STAGES-1] : synch_in)
    );

    // When stages exist, stage 0 captures synch_in on each clock.
    check_stage0_updates_from_in: assert property (
        @(posedge clk) (C_NUM_STAGES > 0 && $past(1'b1)) |-> (synch_d[0] == $past(synch_in))
    );

    // Each stage i (i>=1) captures previous stage (i-1) on each clock.
    generate
        genvar i;
        for (i = 1; i < C_NUM_STAGES; i = i + 1) begin : gen_stage_shift_checks
            // Stage i updates from stage i-1 on the next cycle.
            check_stage_shift: assert property (
                @(posedge clk) $past(1'b1) |-> (synch_d[i] == $past(synch_d[i-1]))
            );
        end
    endgenerate

    // With stages, synch_out equals synch_in delayed by C_NUM_STAGES clocks (after sufficient history).
    check_total_latency: assert property (
        @(posedge clk) ((C_NUM_STAGES > 0) && $past(1'b1, C_NUM_STAGES)) |-> (synch_out == $past(synch_in, C_NUM_STAGES))
    );

    // In bypass mode (no stages), synch_out equals synch_in every cycle.
    check_bypass_behavior: assert property (
        @(posedge clk) (C_NUM_STAGES == 0) |-> (synch_out == synch_in)
    );

    // With stages, any change on synch_out corresponds to a change on synch_in exactly C_NUM_STAGES cycles earlier.
    localparam int N_PLUS1 = (C_NUM_STAGES > 0) ? (C_NUM_STAGES + 1) : 1;
    check_out_change_has_prior_in_change: assert property (
        @(posedge clk)
            (C_NUM_STAGES > 0 && $past(1'b1, N_PLUS1) && (synch_out != $past(synch_out)))
            |-> ($past(synch_in, C_NUM_STAGES) != $past(synch_in, N_PLUS1))
    );

    // In bypass mode, any change on synch_out implies synch_in changed in the same cycle.
    check_bypass_change_causality: assert property (
        @(posedge clk) (C_NUM_STAGES == 0 && $past(1'b1) && (synch_out != $past(synch_out))) |-> (synch_in != $past(synch_in))
    );

    // With stages, synch_out equals the last stage on every clock (sequential consistency).
    check_out_matches_last_stage_each_cycle: assert property (
        @(posedge clk) (C_NUM_STAGES > 0) |-> (synch_out == synch_d[C_NUM_STAGES-1])
    );
endmodule