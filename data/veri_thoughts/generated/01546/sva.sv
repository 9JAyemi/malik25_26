module arithmetic_module_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [1:0] control,
    input logic [3:0] out
);
    // Out follows the case selection: add, subtract, or zero.
    check_case_function: assert property (
        @(posedge clk) out == ((control == 2'b00) ? (a + b) :
                               (control == 2'b01) ? (a - b) :
                               4'b0000)
    );

    // When control==00, out equals a + b.
    check_addition_selected: assert property (
        @(posedge clk) (control == 2'b00) |-> (out == (a + b))
    );

    // When control==01, out equals a - b.
    check_subtraction_selected: assert property (
        @(posedge clk) (control == 2'b01) |-> (out == (a - b))
    );

    // When control==10, out is zero.
    check_default_zero_10: assert property (
        @(posedge clk) (control == 2'b10) |-> (out == 4'b0000)
    );

    // When control==11, out is zero.
    check_default_zero_11: assert property (
        @(posedge clk) (control == 2'b11) |-> (out == 4'b0000)
    );

    // MSB of control high implies out is zero (covers 10 and 11).
    check_default_zero_msb: assert property (
        @(posedge clk) control[1] |-> (out == 4'b0000)
    );
endmodule