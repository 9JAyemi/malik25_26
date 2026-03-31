```systemverilog
module threshold_module_sva(
    input logic [3:0] input_value,
    input logic [1:0] output_value
);
    // Sequential logic is not present, so we use @(posedge clk) for all assertions.
    // No reset signal is present in the RTL, so we do not use disable iff.

    // Check if output_value is 00 when input_value is less than or equal to 5.
    check_low_value: assert property (
        @(posedge clk) (input_value <= 5) |-> (output_value == 2'b00)
    ) else $error("output_value should be 00 when input_value is less than or equal to 5");

    // Check if output_value is 10 when input_value is greater than or equal to THRESHOLD (10).
    check_high_value: assert property (
        @(posedge clk) (input_value >= 10) |-> (output_value == 2'b10)
    ) else $error("output_value should be 10 when input_value is greater than or equal to 10");

    // Check if output_value is 01 when input_value is between 6 and 9.
    check_middle_value: assert property (
        @(posedge clk) (input_value > 5) && (input_value < 10) |-> (output_value == 2'b01)
    ) else $error("output_value should be 01 when input_value is between 6 and 9");
endmodule
```