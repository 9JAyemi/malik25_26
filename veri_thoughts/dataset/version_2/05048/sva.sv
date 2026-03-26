module any_edge_detector_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [7:0] anyedge
);

    // anyedge matches the RTL equation using the two previous input samples.
    check_anyedge_matches_rtl_equation: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate)) |-> (anyedge == (($past(in) ^ $past(in,2)) & $past(in)))
    );

    // anyedge can only assert bits that were high on the previous cycle.
    check_anyedge_subset_of_prev_input: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate)) |-> ((anyedge & ~$past(in)) == 8'h00)
    );

    // anyedge bits must have been low two cycles earlier.
    check_anyedge_excludes_older_high_bits: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate)) |-> ((anyedge & $past(in,2)) == 8'h00)
    );

    // If the input was unchanged across the prior cycle, anyedge must be zero.
    check_unchanged_input_clears_anyedge: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate) && ($past(in) == $past(in,2))) |-> (anyedge == 8'h00)
    );

    // Falling bits from the prior cycle are not reported in anyedge.
    check_falling_bits_not_reported: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate)) |-> ((anyedge & ($past(in,2) & ~$past(in))) == 8'h00)
    );

    // Rising bits from the prior cycle are reported in anyedge.
    check_rising_bits_reported: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate)) |-> ((anyedge & ($past(in) & ~$past(in,2))) == ($past(in) & ~$past(in,2)))
    );

endmodule