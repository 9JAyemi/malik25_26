module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic f
);

// f must equal a & b on the sampled clock edge.
    check_f_matches_and: assert property (
        @(posedge clk) f == (a & b)
    );

// When a is 0, f must be 0 on the sampled clock edge.
    check_f_zero_when_a_zero: assert property (
        @(posedge clk) (a == 1'b0) |-> (f == 1'b0)
    );

// When b is 0, f must be 0 on the sampled clock edge.
    check_f_zero_when_b_zero: assert property (
        @(posedge clk) (b == 1'b0) |-> (f == 1'b0)
    );

// When both a and b are 1, f must be 1 on the sampled clock edge.
    check_f_one_when_both_one: assert property (
        @(posedge clk) (a == 1'b1 && b == 1'b1) |-> (f == 1'b1)
    );

endmodule
