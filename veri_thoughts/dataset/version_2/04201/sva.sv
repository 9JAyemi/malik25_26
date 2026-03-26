module comparator_sva (
    input logic       clk,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic [1:0] out
);

    // When A is greater than B, out must encode greater-than.
    check_gt_encoding: assert property (
        @(posedge clk) (A > B) |-> (out == 2'b01)
    );

    // When A is less than B, out must encode less-than.
    check_lt_encoding: assert property (
        @(posedge clk) (A < B) |-> (out == 2'b10)
    );

    // When A equals B, out must encode equality.
    check_eq_encoding: assert property (
        @(posedge clk) (A == B) |-> (out == 2'b11)
    );

    // out=01 must only occur when A is greater than B.
    check_code_01_means_gt: assert property (
        @(posedge clk) (out == 2'b01) |-> (A > B)
    );

    // out=10 must only occur when A is less than B.
    check_code_10_means_lt: assert property (
        @(posedge clk) (out == 2'b10) |-> (A < B)
    );

    // out=11 must only occur when A equals B.
    check_code_11_means_eq: assert property (
        @(posedge clk) (out == 2'b11) |-> (A == B)
    );

    // The comparator never drives the unused code 00.
    check_no_unused_code: assert property (
        @(posedge clk) out != 2'b00
    );

    // If A and B stay the same, out must also stay the same.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(out)
    );

endmodule