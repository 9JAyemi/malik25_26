module decimal_to_binary_sva (
    input logic [3:0] in_value,
    output logic [3:0] out_value
);
    // Combinational logic, so use @(posedge clk)
    // No clock or reset signals in this module

    // Ensure that out_value is always one-hot encoded for valid input values
    valid_output: assert property (
        @(posedge clk) disable iff (1'b0) (in_value inside {[0:9]}) |-> (out_value == (1 << in_value))
    ) else $error("Invalid output for input value");

    // Ensure that out_value is in an undefined state for invalid input values
    invalid_output: assert property (
        @(posedge clk) disable iff (1'b0) (in_value outside {[0:9]}) |-> (out_value == 4'bXXXX)
    ) else $error("Output should be undefined for invalid input value");

    // Ensure that out_value is always a valid 4-bit binary number
    binary_output: assert property (
        @(posedge clk) disable iff (1'b0) (in_value inside {[0:9]}) |-> (out_value inside {[0:15]})
    ) else $error("Output should be a valid 4-bit binary number");

    // Ensure that out_value is always a power of 2 for valid input values
    power_of_two_output: assert property (
        @(posedge clk) disable iff (1'b0) (in_value inside {[0:9]}) |-> (out_value == (1 << in_value))
    ) else $error("Output should be a power of 2 for valid input value");

    // Ensure that out_value is always zero for input value 0
    zero_output: assert property (
        @(posedge clk) disable iff (1'b0) (in_value == 4'b0000) |-> (out_value == 4'b0000)
    ) else $error("Output should be zero for input value 0");

    // Ensure that out_value is always one for input value 1
    one_output: assert property (
        @(posedge clk) disable iff (1'b0) (in_value == 4'b0001) |-> (out_value == 4'b0001)
    ) else $error("Output should be one for input value 1");

    // Ensure that out_value is always two for input value 2
    two_output: assert property (
        @(posedge clk) disable iff (1'b0) (in_value == 4'b0010) |-> (out_value == 4'b0010)
    ) else $error("Output should be two for input value 2");

    // Ensure that out_value is always three for input value 3
    three_output: assert property (
        @(posedge clk) disable iff (1'b0) (in_value == 4'b0011) |-> (out_value == 4'b0011)
    ) else $error("Output should be three for input value 3");

    // Ensure that out_value is always four for input value 4
    four_output: assert property (
        @(posedge clk) disable iff (1'b0) (in_value == 4'b0100) |-> (out_value == 4'b0100)
    ) else $error("Output should be four for input value 4");

    // Ensure that out_value is always five for input value 5
    five_output: assert property (
        @(posedge clk) disable iff (1'b0) (in_value == 4'b0101) |-> (out_value == 4'b0101)
    ) else $error("Output should be five for input value 5");

    // Ensure that out_value is always six for input value 6
    six_output: assert property (
        @(posedge clk) disable iff (1'b0) (in_value == 4'b0110) |-> (out_value == 4'b0110)
    ) else $error("Output should be six for input value 6");

    // Ensure that out_value is always seven for input value 7
    seven_output: assert property (
        @(posedge clk) disable iff (1'b0) (in_value == 4'b0111) |-> (out_value == 4'b0111)
    ) else $error("Output should be seven for input value 7");

    // Ensure that out_value is always eight for input value 8
    eight_output: assert property (
        @(posedge clk) disable iff (1'b0) (in_value == 4'b1000) |-> (out_value == 4'b1000)
    ) else $error("Output should be eight for input value 8");

    // Ensure that out_value is always nine for input value 9
    nine_output: assert property (
        @(posedge clk) disable iff (1'b0) (in_value == 4'b1001) |-> (out_value == 4'b1001)
    ) else $error("Output should be nine for input value 9");
endmodule