module isSigNaNRecFN_sva #(parameter expWidth = 3, parameter sigWidth = 3) (
    input logic clk,
    input logic [(expWidth + sigWidth):0] in,
    input logic isSigNaN
);

    wire isNaN;
    assign isNaN = (in[(expWidth + sigWidth - 1):(expWidth + sigWidth - 3)] == 3'b111);

    // Output matches the RTL combinational definition.
    check_isSigNaN_definition: assert property (
        @(posedge clk) isSigNaN == (isNaN && !in[sigWidth - 2])
    );

    // A HIGH output requires the checked upper bits to match the NaN pattern.
    check_output_high_requires_nan_pattern: assert property (
        @(posedge clk) isSigNaN |-> isNaN
    );

    // A HIGH output requires the selected significand bit to be LOW.
    check_output_high_requires_clear_indicator_bit: assert property (
        @(posedge clk) isSigNaN |-> !in[sigWidth - 2]
    );

    // The NaN pattern with a clear indicator bit must assert the output.
    check_nan_pattern_with_clear_indicator_sets_output: assert property (
        @(posedge clk) (isNaN && !in[sigWidth - 2]) |-> isSigNaN
    );

    // The NaN pattern with a set indicator bit must deassert the output.
    check_nan_pattern_with_set_indicator_clears_output: assert property (
        @(posedge clk) (isNaN && in[sigWidth - 2]) |-> !isSigNaN
    );

    // Any non-NaN upper-bit pattern must deassert the output.
    check_non_nan_pattern_clears_output: assert property (
        @(posedge clk) !isNaN |-> !isSigNaN
    );

endmodule