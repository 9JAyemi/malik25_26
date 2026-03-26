module reset_synchronizer_sva #(
    parameter NUM_RESET_OUTPUT = 1,
    parameter RESET_SYNC_STAGES = 4
) (
    input  logic reset_n,
    input  logic clk,
    input  logic [NUM_RESET_OUTPUT-1:0] reset_n_sync,
    input  logic [RESET_SYNC_STAGES+NUM_RESET_OUTPUT-2:0] reset_reg
);

    localparam int RESET_REG_WIDTH = RESET_SYNC_STAGES + NUM_RESET_OUTPUT - 1;

    // Async reset clears all synchronizer stages.
    check_reset_reg_cleared_on_reset: assert property (
        @(posedge clk) !reset_n |-> (reset_reg == {RESET_REG_WIDTH{1'b0}})
    );

    // Async reset drives all synchronized reset outputs low.
    check_outputs_cleared_on_reset: assert property (
        @(posedge clk) !reset_n |-> (reset_n_sync == {NUM_RESET_OUTPUT{1'b0}})
    );

    // The output vector matches the selected register slice.
    check_output_vector_mapping: assert property (
        @(posedge clk)
        reset_n_sync == reset_reg[RESET_SYNC_STAGES+NUM_RESET_OUTPUT-2:RESET_SYNC_STAGES-1]
    );

    // Any asserted synchronized reset output requires reset_n to be high.
    check_output_high_requires_reset_high: assert property (
        @(posedge clk) (|reset_n_sync) |-> reset_n
    );

    // Stage 0 is driven high after one clock with reset released.
    check_stage0_sets_high: assert property (
        @(posedge clk) disable iff (!reset_n)
        1'b1 |=> (reset_reg[0] == 1'b1)
    );

    genvar i;
    generate
        for (i = 1; i < RESET_SYNC_STAGES; i = i + 1) begin : gen_shift_stage
            // Each sync stage captures the previous stage.
            check_shift_stage_update: assert property (
                @(posedge clk) disable iff (!reset_n)
                1'b1 |=> (reset_reg[i] == $past(reset_reg[i-1]))
            );
        end
    endgenerate

    generate
        if (RESET_SYNC_STAGES > 1) begin : gen_output_stage_checks
            genvar j;
            for (j = RESET_SYNC_STAGES; j < RESET_SYNC_STAGES + NUM_RESET_OUTPUT - 1; j = j + 1) begin : gen_output_stage
                // Extra output stages copy the last pre-output sync stage.
                check_output_stage_update: assert property (
                    @(posedge clk) disable iff (!reset_n)
                    1'b1 |=> (reset_reg[j] == $past(reset_reg[RESET_SYNC_STAGES-2]))
                );
            end
        end
    endgenerate

    // After reset release, outputs stay low for the sync delay and then assert.
    check_output_release_latency: assert property (
        @(posedge clk) disable iff (!reset_n)
        $rose(reset_n) |-> (reset_n_sync == {NUM_RESET_OUTPUT{1'b0}})[*RESET_SYNC_STAGES] ##1
                          (reset_n_sync == {NUM_RESET_OUTPUT{1'b1}})
    );

endmodule