module comparator_4bit_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] result
);

    // A greater than B must produce the greater-than code.
    check_result_when_a_gt_b: assert property (
        @(posedge clk) (A > B) |-> (result == 2'b01)
    );

    // A less than B must produce the less-than code.
    check_result_when_a_lt_b: assert property (
        @(posedge clk) (A < B) |-> (result == 2'b10)
    );

    // Equal inputs must produce the equal code.
    check_result_when_a_eq_b: assert property (
        @(posedge clk) (A == B) |-> (result == 2'b00)
    );

    // The greater-than code must only appear when A is greater than B.
    check_code_01_means_a_gt_b: assert property (
        @(posedge clk) (result == 2'b01) |-> (A > B)
    );

    // The less-than code must only appear when A is less than B.
    check_code_10_means_a_lt_b: assert property (
        @(posedge clk) (result == 2'b10) |-> (A < B)
    );

    // The equal code must only appear when A and B are equal.
    check_code_00_means_a_eq_b: assert property (
        @(posedge clk) (result == 2'b00) |-> (A == B)
    );

    // The reserved encoding is never driven.
    check_result_encoding_valid: assert property (
        @(posedge clk) (result != 2'b11)
    );

endmodule