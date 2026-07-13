module three_input_module_sva (
    input logic clk,
    input logic input_a,
    input logic input_b,
    input logic input_c,
    input logic output_y
);

    // Output matches the implemented combinational equation.
    check_output_matches_rtl: assert property (
        @(posedge clk)
        output_y == (((input_a | input_b | input_c) && !(input_b & input_c)) ||
                     (input_a && !(input_a & input_b) && !(input_a & input_c)) ||
                     (input_b && !(input_a & input_b) && !(input_b & input_c)) ||
                     (input_c && !(input_a & input_c) && !(input_b & input_c)))
    );

    // Output is LOW when all inputs are LOW.
    check_all_inputs_low: assert property (
        @(posedge clk)
        (!input_a && !input_b && !input_c) |-> !output_y
    );

    // Output is HIGH when input_a is HIGH and input_b/input_c are not both HIGH.
    check_input_a_without_bc_pair: assert property (
        @(posedge clk)
        (input_a && !(input_b && input_c)) |-> output_y
    );

    // Output is HIGH when input_a is LOW and exactly one of input_b/input_c is HIGH.
    check_exactly_one_of_b_or_c_without_a: assert property (
        @(posedge clk)
        (!input_a && ((input_b && !input_c) || (!input_b && input_c))) |-> output_y
    );

    // Output is LOW whenever input_b and input_c are both HIGH.
    check_b_and_c_force_low: assert property (
        @(posedge clk)
        (input_b && input_c) |-> !output_y
    );

endmodule