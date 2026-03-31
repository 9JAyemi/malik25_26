module simple_calculator_sva (
    input logic signed [7:0] a,
    input logic signed [7:0] b,
    input logic signed [7:0] add_out,
    input logic signed [7:0] sub_out,
    input logic signed [7:0] mul_out,
    input logic signed [7:0] div_out,
    input logic [1:0] op
);

    // op=00 selects addition and drives add_out.
    check_add_mode: assert property (
        @($global_clock) (op == 2'b00) |-> ((add_out == (a + b)) &&
                                           (sub_out == 8'sd0) &&
                                           (mul_out == 8'sd0) &&
                                           (div_out == 8'sd0))
    );

    // op=01 selects subtraction and drives sub_out.
    check_sub_mode: assert property (
        @($global_clock) (op == 2'b01) |-> ((add_out == 8'sd0) &&
                                           (sub_out == (a - b)) &&
                                           (mul_out == 8'sd0) &&
                                           (div_out == 8'sd0))
    );

    // op=10 selects multiplication and drives mul_out.
    check_mul_mode: assert property (
        @($global_clock) (op == 2'b10) |-> ((add_out == 8'sd0) &&
                                           (sub_out == 8'sd0) &&
                                           (mul_out == (a * b)) &&
                                           (div_out == 8'sd0))
    );

    // op=11 selects division and drives div_out.
    check_div_mode: assert property (
        @($global_clock) (op == 2'b11) |-> ((add_out == 8'sd0) &&
                                           (sub_out == 8'sd0) &&
                                           (mul_out == 8'sd0) &&
                                           (div_out == (a / b)))
    );

    // add_out is always zero when op is not 00.
    check_add_out_zero_when_not_add: assert property (
        @($global_clock) (op != 2'b00) |-> (add_out == 8'sd0)
    );

    // sub_out is always zero when op is not 01.
    check_sub_out_zero_when_not_sub: assert property (
        @($global_clock) (op != 2'b01) |-> (sub_out == 8'sd0)
    );

    // mul_out is always zero when op is not 10.
    check_mul_out_zero_when_not_mul: assert property (
        @($global_clock) (op != 2'b10) |-> (mul_out == 8'sd0)
    );

    // div_out is always zero when op is not 11.
    check_div_out_zero_when_not_div: assert property (
        @($global_clock) (op != 2'b11) |-> (div_out == 8'sd0)
    );

endmodule