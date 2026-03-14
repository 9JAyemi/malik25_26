module react_sva (
    input logic pipelineReady,
    input logic scheduleTask,
    input logic [2:0] workCounter,
    input logic scryptResultAvailableIn,
    input logic doWork,
    input logic [7:0] preparing,
    input logic decreasePrepare,
    input logic scryptResultAvailable
);
    // decreasePrepare must be 0 when scryptResultAvailableIn is 1.
    decprep_low_when_scryptin_high: assert property (
        @(posedge scryptResultAvailableIn) (decreasePrepare == 1'b0)
    );

    // decreasePrepare must be 1 when scryptResultAvailableIn is 0.
    decprep_high_when_scryptin_low: assert property (
        @(negedge scryptResultAvailableIn) (decreasePrepare == 1'b1)
    );

    // scryptResultAvailableIn must be 0 when decreasePrepare rises.
    scryptin_low_on_decprep_rise: assert property (
        @(posedge decreasePrepare) (scryptResultAvailableIn == 1'b0)
    );

    // scryptResultAvailableIn must be 1 when decreasePrepare falls.
    scryptin_high_on_decprep_fall: assert property (
        @(negedge decreasePrepare) (scryptResultAvailableIn == 1'b1)
    );

    // scryptResultAvailable equals (preparing > 0) when sampled on scryptResultAvailableIn rising edge.
    result_flag_matches_prep_on_scryptin_rise: assert property (
        @(posedge scryptResultAvailableIn) (scryptResultAvailable == (preparing > 8'd0))
    );

    // scryptResultAvailable equals (preparing > 0) when sampled on scryptResultAvailableIn falling edge.
    result_flag_matches_prep_on_scryptin_fall: assert property (
        @(negedge scryptResultAvailableIn) (scryptResultAvailable == (preparing > 8'd0))
    );

    // If scryptResultAvailable rises, preparing must be > 0 at that time.
    result_flag_rise_requires_positive_prep: assert property (
        @(posedge scryptResultAvailable) (preparing > 8'd0)
    );

    // If scryptResultAvailable falls, preparing must be 0 at that time.
    result_flag_fall_requires_zero_prep: assert property (
        @(negedge scryptResultAvailable) (preparing == 8'd0)
    );

    // Increment and decrement conditions for preparing cannot be true simultaneously.
    inc_dec_conditions_mutex: assert property (
        @(posedge scryptResultAvailableIn)
            !(
                (pipelineReady && scheduleTask && (workCounter == 3'd3) && !decreasePrepare && !doWork) &&
                (!pipelineReady && !scheduleTask && decreasePrepare && !doWork)
            )
    );

    // No preparing update condition is true when doWork is HIGH.
    no_update_when_doWork_high: assert property (
        @(posedge scryptResultAvailableIn)
            doWork |-> !(
                (pipelineReady && scheduleTask && (workCounter == 3'd3) && !decreasePrepare && !doWork) ||
                (!pipelineReady && !scheduleTask && decreasePrepare && !doWork)
            )
    );
endmodule