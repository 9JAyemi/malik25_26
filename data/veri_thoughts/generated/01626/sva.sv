module check_1fs_sva (
    input logic CLK,
    input logic [31:0] timeunit,
    input logic [31:0] timeprecision,
    input logic is_1fs
);
    // Output high when both inputs are exactly 1.
    check_is_1fs_high_when_both_one: assert property (
        @(posedge CLK) ((timeunit === 32'd1) && (timeprecision === 32'd1)) |-> (is_1fs == 1'b1)
    );

    // Output low when either input is not exactly 1.
    check_is_1fs_low_when_any_not_one: assert property (
        @(posedge CLK) ((timeunit !== 32'd1) || (timeprecision !== 32'd1)) |-> (is_1fs == 1'b0)
    );

    // If output is high, both inputs must be exactly 1.
    check_output_high_implies_inputs_one: assert property (
        @(posedge CLK) (is_1fs == 1'b1) |-> ((timeunit === 32'd1) && (timeprecision === 32'd1))
    );

    // Rising edge on output only when both inputs are exactly 1.
    check_rise_requires_both_one: assert property (
        @(posedge CLK) $rose(is_1fs) |-> ((timeunit === 32'd1) && (timeprecision === 32'd1))
    );

    // Falling edge on output only when at least one input is not exactly 1.
    check_fall_requires_any_not_one: assert property (
        @(posedge CLK) $fell(is_1fs) |-> ((timeunit !== 32'd1) || (timeprecision !== 32'd1))
    );

    // Output is never X or Z.
    check_output_known: assert property (
        @(posedge CLK) !$isunknown(is_1fs)
    );
endmodule