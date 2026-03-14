module and3_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X,
    input logic and0_out,
    input logic and1_out
);
    // and0_out equals A & B
    check_and0_out_function: assert property (
        @(posedge clk) and0_out == (A & B)
    );

    // and1_out equals C & and0_out
    check_and1_out_function: assert property (
        @(posedge clk) and1_out == (C & and0_out)
    );

    // X is driven by and1_out
    check_x_equals_and1_out: assert property (
        @(posedge clk) X == and1_out
    );

    // X equals A & B & C
    check_x_equals_abc: assert property (
        @(posedge clk) X == (A & B & C)
    );

    // If X is 1 then all inputs are 1
    check_x_high_requires_all_high: assert property (
        @(posedge clk) (X == 1'b1) |-> (A && B && C)
    );

    // If any input is 0 then X is 0
    check_any_input_low_forces_x_low: assert property (
        @(posedge clk) ((!A) || (!B) || (!C)) |-> (X == 1'b0)
    );

    // If all inputs are 1 then X is 1
    check_all_inputs_high_imply_x_high: assert property (
        @(posedge clk) (A && B && C) |-> (X == 1'b1)
    );

    // Rising edge of X implies all inputs are 1
    check_x_rise_requires_all_high: assert property (
        @(posedge clk) $rose(X) |-> (A && B && C)
    );

    // Falling edge of X implies at least one input is 0
    check_x_fall_implies_any_low: assert property (
        @(posedge clk) $fell(X) |-> (!A || !B || !C)
    );
endmodule