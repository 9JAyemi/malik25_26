module mux4to1_sva (
    input logic clk,
    input logic I0,
    input logic I1,
    input logic I2,
    input logic I3,
    input logic S,
    input logic O
);

    // O matches the implemented XOR of the two selected branches.
    check_output_equation: assert property (
        @(posedge clk)
        O == ((((~S) & I0) | (S & I1)) ^ (((~S) & I2) | (S & I3)))
    );

    // With S low, O is the XOR of I0 and I2.
    check_select_low_function: assert property (
        @(posedge clk)
        (S == 1'b0) |-> (O == (I0 ^ I2))
    );

    // With S high, O is the XOR of I1 and I3.
    check_select_high_function: assert property (
        @(posedge clk)
        (S == 1'b1) |-> (O == (I1 ^ I3))
    );

    // With S low, equal selected inputs drive O low.
    check_select_low_equal_inputs_zero: assert property (
        @(posedge clk)
        ((S == 1'b0) && (I0 == I2)) |-> (O == 1'b0)
    );

    // With S low, different selected inputs drive O high.
    check_select_low_different_inputs_one: assert property (
        @(posedge clk)
        ((S == 1'b0) && (I0 != I2)) |-> (O == 1'b1)
    );

    // With S high, equal selected inputs drive O low.
    check_select_high_equal_inputs_zero: assert property (
        @(posedge clk)
        ((S == 1'b1) && (I1 == I3)) |-> (O == 1'b0)
    );

    // With S high, different selected inputs drive O high.
    check_select_high_different_inputs_one: assert property (
        @(posedge clk)
        ((S == 1'b1) && (I1 != I3)) |-> (O == 1'b1)
    );

endmodule