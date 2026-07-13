module minimum_value_sva (
    input logic       clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    input logic [7:0] min_val_out
);

    // Combinational DUT sampled on clk; no reset is present in the RTL.

    // Checks the output matches the RTL min-selection expression.
    check_output_matches_rtl_expression: assert property (
        @(posedge clk)
        min_val_out == ((a < b) ? ((a < c) ? ((a < d) ? a : d) : ((c < d) ? c : d))
                                : ((b < c) ? ((b < d) ? b : d) : ((c < d) ? c : d)))
    );

    // Checks the output is not greater than input a.
    check_output_le_a: assert property (
        @(posedge clk)
        min_val_out <= a
    );

    // Checks the output is not greater than input b.
    check_output_le_b: assert property (
        @(posedge clk)
        min_val_out <= b
    );

    // Checks the output is not greater than input c.
    check_output_le_c: assert property (
        @(posedge clk)
        min_val_out <= c
    );

    // Checks the output is not greater than input d.
    check_output_le_d: assert property (
        @(posedge clk)
        min_val_out <= d
    );

    // Checks the output matches one of the input values.
    check_output_is_one_of_inputs: assert property (
        @(posedge clk)
        (min_val_out == a) || (min_val_out == b) || (min_val_out == c) || (min_val_out == d)
    );

    // Checks a is produced when a is less than or equal to all inputs.
    check_select_a_when_a_is_minimum: assert property (
        @(posedge clk)
        (a <= b && a <= c && a <= d) |-> (min_val_out == a)
    );

    // Checks b is produced when b is less than or equal to all inputs.
    check_select_b_when_b_is_minimum: assert property (
        @(posedge clk)
        (b <= a && b <= c && b <= d) |-> (min_val_out == b)
    );

    // Checks c is produced when c is less than or equal to all inputs.
    check_select_c_when_c_is_minimum: assert property (
        @(posedge clk)
        (c <= a && c <= b && c <= d) |-> (min_val_out == c)
    );

    // Checks d is produced when d is less than or equal to all inputs.
    check_select_d_when_d_is_minimum: assert property (
        @(posedge clk)
        (d <= a && d <= b && d <= c) |-> (min_val_out == d)
    );

endmodule