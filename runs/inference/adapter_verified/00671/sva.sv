module xor_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out_comb
);

// out_comb must match the RTL expression.
    check_out_matches_rtl_expr: assert property (
        @(posedge clk) out_comb == ((a & ~b) | (~a & b))
    );

// When a is 0 and b is 1, out_comb must be 1.
    check_a0_b1_sets_out: assert property (
        @(posedge clk) (a == 1'b0 && b == 1'b1) |-> (out_comb == 1'b1)
    );

// When a is 1 and b is 0, out_comb must be 1.
    check_a1_b0_sets_out: assert property (
        @(posedge clk) (a == 1'b1 && b == 1'b0) |-> (out_comb == 1'b1)
    );

// When a equals b, out_comb must be 0.
    check_equal_inputs_clear_out: assert property (
        @(posedge clk) (a == b) |-> (out_comb == 1'b0)
    );

// When a is 1 and b is 1, out_comb must be 0.
    check_a1_b1_clears_out: assert property (
        @(posedge clk) (a == 1'b1 && b == 1'b1) |-> (out_comb == 1'b0)
    );

// When a is 0 and b is 0, out_comb must be 0.
    check_a0_b0_clears_out: assert property (
        @(posedge clk) (a == 1'b0 && b == 1'b0) |-> (out_comb == 1'b0)
    );

endmodule
