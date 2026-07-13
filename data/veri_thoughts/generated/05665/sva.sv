module calculator_sva(
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic op,
    input logic [3:0] out
);

    // Addition mode drives out to a + b.
    check_addition_result: assert property (
        @(posedge clk) (op == 1'b0) |-> (out == (a + b))
    );

    // Subtraction mode drives out to a - b.
    check_subtraction_result: assert property (
        @(posedge clk) (op == 1'b1) |-> (out == (a - b))
    );

    // Stable inputs keep the sampled output stable.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk) $stable({a, b, op}) |-> $stable(out)
    );

endmodule