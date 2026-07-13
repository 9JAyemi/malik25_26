module priority_encoder_4to2_sva (
    input logic [3:0] I,
    input logic clk,
    input logic [1:0] Y
);

    // Y reflects the previous cycle's selected input pair.
    check_output_from_prev_inputs: assert property (
        @(posedge clk)
        1'b1 |=> (Y == ($past(I[1]) ? {1'b1, $past(I[0])} :
                      ($past(I[3]) ? {1'b1, $past(I[2])} : 2'b00)))
    );

    // The lower input pair is selected whenever its valid bit is high.
    check_lower_pair_selected: assert property (
        @(posedge clk)
        (I[1] == 1'b1) |=> (Y == {1'b1, $past(I[0])})
    );

    // The upper input pair is selected when the lower pair is invalid.
    check_upper_pair_selected: assert property (
        @(posedge clk)
        ((I[1] == 1'b0) && (I[3] == 1'b1)) |=> (Y == {1'b1, $past(I[2])})
    );

    // The output clears when neither input pair is valid.
    check_zero_when_no_valid_pair: assert property (
        @(posedge clk)
        ((I[1] == 1'b0) && (I[3] == 1'b0)) |=> (Y == 2'b00)
    );

    // When both pairs are valid, the lower pair has priority.
    check_lower_pair_priority: assert property (
        @(posedge clk)
        ((I[1] == 1'b1) && (I[3] == 1'b1)) |=> (Y == {1'b1, $past(I[0])})
    );

    // Y[1] shows whether either pair was valid in the previous cycle.
    check_output_msb_valid: assert property (
        @(posedge clk)
        1'b1 |=> (Y[1] == ($past(I[1]) | $past(I[3])))
    );

    // Y[0] comes from the previously selected pair.
    check_output_lsb_source: assert property (
        @(posedge clk)
        1'b1 |=> (Y[0] == ($past(I[1]) ? $past(I[0]) :
                          ($past(I[3]) ? $past(I[2]) : 1'b0)))
    );

endmodule