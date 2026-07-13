module Incrementer_sva (
    input logic clk,                // external verification clock (RTL has no clock/reset)
    input logic [7:0] inValue,
    input logic [7:0] outValue
);
    // When input is 0xFF, output wraps to 0x00.
    check_wrap_when_max: assert property (
        @(posedge clk) (inValue == 8'hFF) |-> (outValue == 8'h00)
    );

    // When input is not 0xFF, output equals input + 1.
    check_increment_nonmax: assert property (
        @(posedge clk) (inValue != 8'hFF) |-> (outValue == inValue + 8'd1)
    );

    // Only max input (0xFF) can produce output 0x00.
    check_zero_only_from_max: assert property (
        @(posedge clk) (outValue == 8'h00) |-> (inValue == 8'hFF)
    );

    // Output 0xFF occurs only when input is 0xFE.
    check_out_ff_implies_in_fe: assert property (
        @(posedge clk) (outValue == 8'hFF) |-> (inValue == 8'hFE)
    );

    // Output is never equal to input (no fixed point for +1 mod 256).
    check_out_never_equals_in: assert property (
        @(posedge clk) (outValue != inValue)
    );

    // Output minus input is always 1 mod 256.
    check_modulo_difference_one: assert property (
        @(posedge clk) ((outValue - inValue) == 8'h01)
    );

    // If input is stable across cycles, output is stable as well.
    check_stable_when_input_stable: assert property (
        @(posedge clk) $stable(inValue) |-> $stable(outValue)
    );

    // For non-max input, output is strictly greater than input.
    check_monotonic_nonmax: assert property (
        @(posedge clk) (inValue != 8'hFF) |-> (outValue > inValue)
    );
endmodule