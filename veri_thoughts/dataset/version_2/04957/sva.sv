module larger_number_sva (
    input logic        clk,
    input logic [3:0]  num1,
    input logic [3:0]  num2,
    input logic [3:0]  larger
);

    // When num1 is greater than num2, larger must equal num1.
    check_num1_selected_when_greater: assert property (
        @(posedge clk) (num1 > num2) |-> (larger == num1)
    );

    // When num2 is greater than num1, larger must equal num2.
    check_num2_selected_when_greater: assert property (
        @(posedge clk) (num2 > num1) |-> (larger == num2)
    );

    // When the inputs are equal, larger must equal that common value.
    check_equal_inputs_return_value: assert property (
        @(posedge clk) (num1 == num2) |-> (larger == num1)
    );

    // The output must always match the RTL's max-selection behavior.
    check_output_matches_max_function: assert property (
        @(posedge clk) larger == ((num1 >= num2) ? num1 : num2)
    );

    // The output must always be one of the input values.
    check_output_is_one_of_inputs: assert property (
        @(posedge clk) (larger == num1) || (larger == num2)
    );

    // The output must not be smaller than num1.
    check_output_not_smaller_than_num1: assert property (
        @(posedge clk) larger >= num1
    );

    // The output must not be smaller than num2.
    check_output_not_smaller_than_num2: assert property (
        @(posedge clk) larger >= num2
    );

endmodule