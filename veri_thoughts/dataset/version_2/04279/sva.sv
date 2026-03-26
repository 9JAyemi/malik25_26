module tri_buf_sva (
    input logic clk,
    input logic in,
    input logic en,
    input logic out
);

    // Output must implement the RTL ternary function.
    check_out_matches_function: assert property (
        @(posedge clk) out == (en ? in : 1'b1)
    );

    // When enabled, output must follow input.
    check_out_follows_input_when_enabled: assert property (
        @(posedge clk) en |-> (out == in)
    );

    // When disabled, output must be driven high.
    check_out_high_when_disabled: assert property (
        @(posedge clk) !en |-> (out == 1'b1)
    );

    // A low output is only possible when enabled with a low input.
    check_low_out_requires_enabled_low_input: assert property (
        @(posedge clk) !out |-> (en && !in)
    );

endmodule