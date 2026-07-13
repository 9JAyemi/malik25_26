module and_or_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic g_out,
    input logic p_out
);

// g_out must equal a AND b.
    check_g_out_and: assert property (
        @(posedge clk) g_out == (a & b)
    );

// p_out must equal a OR b.
    check_p_out_or: assert property (
        @(posedge clk) p_out == (a | b)
    );

// If both inputs are 1, both outputs must be 1.
    check_both_high: assert property (
        @(posedge clk) (a && b) |-> (g_out && p_out)
    );

// If either input is 0, g_out must be 0.
    check_g_out_zero_when_any_zero: assert property (
        @(posedge clk) (!a || !b) |-> !g_out
    );

// If either input is 1, p_out must be 1.
    check_p_out_one_when_any_one: assert property (
        @(posedge clk) (a || b) |-> p_out
    );

// If both inputs are 0, both outputs must be 0.
    check_both_low: assert property (
        @(posedge clk) (!a && !b) |-> (!g_out && !p_out)
    );

endmodule
