module simple_calculator_sva (
    input logic signed [7:0] a,
    input logic signed [7:0] b,
    input logic signed [7:0] add_out,
    input logic signed [7:0] sub_out,
    input logic signed [7:0] mul_out,
    input logic signed [7:0] div_out,
    input logic [1:0]        op
);

    // Addition mode drives only add_out and clears the other outputs.
    check_add_mode_outputs: assert property (
        @($global_clock)
        (op == 2'b00) |-> ((add_out == (a + b)) &&
                           (sub_out == 8'sd0) &&
                           (mul_out == 8'sd0) &&
                           (div_out == 8'sd0))
    );

    // Subtraction mode drives only sub_out and clears the other outputs.
    check_sub_mode_outputs: assert property (
        @($global_clock)
        (op == 2'b01) |-> ((add_out == 8'sd0) &&
                           (sub_out == (a - b)) &&
                           (mul_out == 8'sd0) &&
                           (div_out == 8'sd0))
    );

    // Multiplication mode drives only mul_out and clears the other outputs.
    check_mul_mode_outputs: assert property (
        @($global_clock)
        (op == 2'b10) |-> ((add_out == 8'sd0) &&
                           (sub_out == 8'sd0) &&
                           (mul_out == (a * b)) &&
                           (div_out == 8'sd0))
    );

    // Division mode drives only div_out and clears the other outputs.
    check_div_mode_outputs: assert property (
        @($global_clock)
        (op == 2'b11) |-> ((add_out == 8'sd0) &&
                           (sub_out == 8'sd0) &&
                           (mul_out == 8'sd0) &&
                           (div_out == (a / b)))
    );

    // With stable inputs, the outputs remain stable.
    check_stable_inputs_hold_outputs: assert property (
        @($global_clock)
        ($stable(a) && $stable(b) && $stable(op)) |-> $stable({add_out, sub_out, mul_out, div_out})
    );

    // In addition mode, changing only b updates only add_out.
    check_add_mode_b_change: assert property (
        @($global_clock)
        (op == 2'b00 && $stable(a) && !$stable(b)) |-> ($stable(add_out) &&
                                                        !$stable(sub_out) &&
                                                        !$stable(mul_out) &&
                                                        !$stable(div_out))
    );

    // In subtraction mode, changing only b updates only sub_out.
    check_sub_mode_b_change: assert property (
        @($global_clock)
        (op == 2'b01 && $stable(a) && !$stable(b)) |-> ($stable(sub_out) &&
                                                        !$stable(add_out) &&
                                                        !$stable(mul_out) &&
                                                        !$stable(div_out))
    );

    // In multiplication mode, changing only b updates only mul_out.
    check_mul_mode_b_change: assert property (
        @($global_clock)
        (op == 2'b10 && $stable(a) && !$stable(b)) |-> ($stable(mul_out) &&
                                                        !$stable(add_out) &&
                                                        !$stable(sub_out) &&
                                                        !$stable(div_out))
    );

    // In division mode, changing only b updates only div_out.
    check_div_mode_b_change: assert property (
        @($global_clock)
        (op == 2'b11 && $stable(a) && !$stable(b)) |-> ($stable(div_out) &&
                                                        !$stable(add_out) &&
                                                        !$stable(sub_out) &&
                                                        !$stable(mul_out))
    );

endmodule