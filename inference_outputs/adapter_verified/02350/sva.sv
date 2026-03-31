module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic reset,
    input logic out
);

// Reset forces the output low.
    check_reset_forces_out_low: assert property (
        @(posedge clk) reset |-> (out == 1'b0)
    );

// With reset low, out equals a ^ b ^ c.
    check_function_when_not_reset: assert property (
        @(posedge clk) disable iff (reset) (out == (a ^ b ^ c))
    );

// A high output requires all three inputs to be high.
    check_out_high_requires_all_high: assert property (
        @(posedge clk) disable iff (reset) out |-> (a && b && c)
    );

// All three inputs high produce a high output.
    check_all_high_produces_out_high: assert property (
        @(posedge clk) disable iff (reset) (a && b && c) |-> out
    );

// Any low input forces the output low.
    check_any_low_forces_out_low: assert property (
        @(posedge clk) disable iff (reset) (!a || !b || !c) |-> (out == 1'b0)
    );

endmodule
