module my_nor_assert (
    input logic clk,
    input logic a,
    input logic b,
    input logic y
);
    ///// NOR function checks /////
    // y must equal NOR of a and b.
    check_y_is_nor: assert property (
        @(posedge clk) y == ~(a | b)
    );

    // If a is 1, y must be 0.
    check_y_zero_if_a_one: assert property (
        @(posedge clk) (a == 1'b1) |-> (y == 1'b0)
    );

    // If b is 1, y must be 0.
    check_y_zero_if_b_one: assert property (
        @(posedge clk) (b == 1'b1) |-> (y == 1'b0)
    );

    // If both a and b are 0, y must be 1.
    check_y_one_if_both_zero: assert property (
        @(posedge clk) (a == 1'b0 && b == 1'b0) |-> (y == 1'b1)
    );

    // If y is 1, both inputs must be 0.
    check_inputs_zero_if_y_one: assert property (
        @(posedge clk) (y == 1'b1) |-> (a == 1'b0 && b == 1'b0)
    );

    // If y is 0, at least one input must be 1.
    check_some_input_one_if_y_zero: assert property (
        @(posedge clk) (y == 1'b0) |-> (a == 1'b1 || b == 1'b1)
    );
endmodule