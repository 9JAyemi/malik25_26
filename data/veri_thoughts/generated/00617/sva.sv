module and_or_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic g_out,
    input logic p_out
);
    // g_out equals logical AND of inputs.
    check_g_out_is_and: assert property (
        @(posedge clk) g_out == (a & b)
    );

    // p_out equals logical OR of inputs.
    check_p_out_is_or: assert property (
        @(posedge clk) p_out == (a | b)
    );

    // If AND output is 1, OR output must also be 1.
    check_and_implies_or: assert property (
        @(posedge clk) g_out |-> p_out
    );

    // When both inputs are 0, both outputs must be 0.
    check_zero_zero_outputs_zero: assert property (
        @(posedge clk) (!a && !b) |-> (!g_out && !p_out)
    );

    // When a=1 and b=0, outputs must be g_out=0, p_out=1.
    check_a1_b0_outputs: assert property (
        @(posedge clk) (a && !b) |-> (!g_out && p_out)
    );

    // When a=0 and b=1, outputs must be g_out=0, p_out=1.
    check_a0_b1_outputs: assert property (
        @(posedge clk) (!a && b) |-> (!g_out && p_out)
    );

    // When both inputs are 1, both outputs must be 1.
    check_one_one_outputs_one: assert property (
        @(posedge clk) (a && b) |-> (g_out && p_out)
    );
endmodule