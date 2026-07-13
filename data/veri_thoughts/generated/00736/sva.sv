module three_input_module_sva (
    input logic CLK,
    // DUT ports
    input logic input_a,
    input logic input_b,
    input logic input_c,
    input logic output_x,
    input logic vpwr,
    input logic vgnd,
    // DUT internal nets
    input logic or1_output,
    input logic or2_output,
    input logic or3_output
);

    // or1_output equals A|B|C.
    check_or1_function: assert property (
        @(posedge CLK) (or1_output == (input_a | input_b | input_c))
    );

    // or2_output equals A|B|or1_output.
    check_or2_function: assert property (
        @(posedge CLK) (or2_output == (input_a | input_b | or1_output))
    );

    // or3_output equals or2_output|C|or1_output.
    check_or3_function: assert property (
        @(posedge CLK) (or3_output == (or2_output | input_c | or1_output))
    );

    // output_x is inversion of or3_output.
    check_output_inversion: assert property (
        @(posedge CLK) (output_x == ~or3_output)
    );

    // or2_output collapses to or1_output.
    check_or2_equals_or1: assert property (
        @(posedge CLK) (or2_output == or1_output)
    );

    // or3_output collapses to or1_output.
    check_or3_equals_or1: assert property (
        @(posedge CLK) (or3_output == or1_output)
    );

    // output_x equals NOR of inputs.
    check_output_nor_of_inputs: assert property (
        @(posedge CLK) (output_x == ~(input_a | input_b | input_c))
    );

    // When all inputs are 0, output_x must be 1.
    check_all_zero_inputs_output_high: assert property (
        @(posedge CLK) (!input_a && !input_b && !input_c) |=> (output_x == 1'b1)
    );

    // When any input is 1, output_x must be 0.
    check_any_input_high_output_low: assert property (
        @(posedge CLK) (input_a || input_b || input_c) |=> (output_x == 1'b0)
    );

    // If output_x is 1, then all inputs must be 0.
    check_output_high_implies_all_inputs_zero: assert property (
        @(posedge CLK) (output_x == 1'b1) |=> (!input_a && !input_b && !input_c)
    );

endmodule