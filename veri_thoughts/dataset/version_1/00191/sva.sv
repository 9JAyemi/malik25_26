module my_module_sva (
    input logic       clk,
    input logic [3:0] data_in,
    input logic       data_out
);

    // Sampled inputs at or below 5 must drive the output high on the next cycle.
    check_low_or_equal_threshold_drives_high: assert property (
        @(posedge clk) (data_in <= 4'd5) |=> (data_out == 1'b1)
    );

    // Sampled inputs above 5 must drive the output low on the next cycle.
    check_above_threshold_drives_low: assert property (
        @(posedge clk) (data_in > 4'd5) |=> (data_out == 1'b0)
    );

    // The output must match the previous cycle's sampled input compared against 5.
    check_output_matches_previous_input: assert property (
        @(posedge clk) 1'b1 |=> (data_out == (($past(data_in) <= 4'd5) ? 1'b1 : 1'b0))
    );

    // The threshold comparison must include the boundary value 5.
    check_boundary_five_is_high: assert property (
        @(posedge clk) (data_in == 4'd5) |=> (data_out == 1'b1)
    );

    // The first value above the threshold, 6, must drive the output low.
    check_boundary_six_is_low: assert property (
        @(posedge clk) (data_in == 4'd6) |=> (data_out == 1'b0)
    );

endmodule