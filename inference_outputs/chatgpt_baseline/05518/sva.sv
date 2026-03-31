module reset_sync_sva #(
    parameter RESET_SYNC_STAGES = 4,
    parameter NUM_RESET_OUTPUT = 1
) (
    input  logic                          reset_n,
    input  logic                          clk,
    input  logic [NUM_RESET_OUTPUT-1:0]   reset_n_sync
);

    localparam logic [NUM_RESET_OUTPUT-1:0] ALL_ZERO = {NUM_RESET_OUTPUT{1'b0}};
    localparam logic [NUM_RESET_OUTPUT-1:0] ALL_ONE  = {NUM_RESET_OUTPUT{1'b1}};

    genvar d;

    // Reset forces all synchronized reset outputs low.
    check_reset_forces_low: assert property (
        @(posedge clk)
        !reset_n |-> (reset_n_sync == ALL_ZERO)
    );

    generate
        if (RESET_SYNC_STAGES > 1) begin : gen_multi_stage_checks
            for (d = 0; d < RESET_SYNC_STAGES-1; d = d + 1) begin : gen_release_low_cycles
                // Output stays low before the release delay expires.
                check_release_low_before_assert: assert property (
                    @(posedge clk) disable iff (!reset_n)
                    $rose(reset_n) |-> ##d (reset_n_sync == ALL_ZERO)
                );
            end

            // Output asserts after the programmed number of clocks.
            check_release_asserts_after_delay: assert property (
                @(posedge clk) disable iff (!reset_n)
                $rose(reset_n) |-> ##(RESET_SYNC_STAGES-1) (reset_n_sync == ALL_ONE)
            );

            // Output stays high one clock after it asserts.
            check_release_stays_high_next_cycle: assert property (
                @(posedge clk) disable iff (!reset_n)
                $rose(reset_n) |-> ##RESET_SYNC_STAGES (reset_n_sync == ALL_ONE)
            );
        end
        else begin : gen_single_stage_checks
            // A single-stage case asserts on the first clock after release.
            check_release_asserts_immediately: assert property (
                @(posedge clk) disable iff (!reset_n)
                $rose(reset_n) |-> (reset_n_sync == ALL_ONE)
            );

            // A single-stage case stays high one clock later.
            check_release_stays_high_next_cycle: assert property (
                @(posedge clk) disable iff (!reset_n)
                $rose(reset_n) |-> ##1 (reset_n_sync == ALL_ONE)
            );
        end
    endgenerate

endmodule