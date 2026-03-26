module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out
);

    // Output matches the RTL AND expression.
    check_out_matches_and: assert property (
        @(posedge clk) out === ((a & b) ? 1'b1 : 1'b0)
    );

    // Both high inputs drive the output high.
    check_out_high_when_both_high: assert property (
        @(posedge clk) ((a === 1'b1) && (b === 1'b1)) |-> (out === 1'b1)
    );

    // A low on input a forces the output low.
    check_out_low_when_a_low: assert property (
        @(posedge clk) (a === 1'b0) |-> (out === 1'b0)
    );

    // A low on input b forces the output low.
    check_out_low_when_b_low: assert property (
        @(posedge clk) (b === 1'b0) |-> (out === 1'b0)
    );

    // A high output requires both inputs high.
    check_out_high_only_if_both_high: assert property (
        @(posedge clk) (out === 1'b1) |-> ((a === 1'b1) && (b === 1'b1))
    );

endmodule