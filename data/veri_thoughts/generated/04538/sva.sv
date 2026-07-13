module logic_gates_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic out_and,
    input logic out_or,
    input logic out_not,
    input logic out_xor,
    input logic out_xnor
);

    // AND output matches in1 & in2.
    check_and_function: assert property (
        @(posedge clk) out_and == (in1 & in2)
    );

    // OR output matches in1 | in2.
    check_or_function: assert property (
        @(posedge clk) out_or == (in1 | in2)
    );

    // NOT output matches ~in1.
    check_not_function: assert property (
        @(posedge clk) out_not == (~in1)
    );

    // XOR output matches in1 ^ in2.
    check_xor_function: assert property (
        @(posedge clk) out_xor == (in1 ^ in2)
    );

    // XNOR output matches ~(in1 ^ in2).
    check_xnor_function: assert property (
        @(posedge clk) out_xnor == (~(in1 ^ in2))
    );

    // XOR and XNOR are complements.
    check_xor_xnor_complement: assert property (
        @(posedge clk) out_xnor == (~out_xor)
    );

    // Equal inputs drive XNOR high and XOR low.
    check_equal_inputs_behavior: assert property (
        @(posedge clk) (in1 == in2) |-> (out_xnor && !out_xor)
    );

    // Different inputs drive XOR high and XNOR low.
    check_different_inputs_behavior: assert property (
        @(posedge clk) (in1 != in2) |-> (out_xor && !out_xnor)
    );

endmodule