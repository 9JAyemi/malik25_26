module comparator_4bit_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [1:0] res
);

    // Result matches the full comparator function.
    check_complete_result_mapping: assert property (
        @(posedge clk) res == ((a > b) ? 2'b01 : ((a < b) ? 2'b10 : 2'b11))
    );

    // Greater-than case produces 01.
    check_gt_result_encoding: assert property (
        @(posedge clk) (a > b) |-> (res == 2'b01)
    );

    // Less-than case produces 10.
    check_lt_result_encoding: assert property (
        @(posedge clk) (a < b) |-> (res == 2'b10)
    );

    // Equality case produces 11.
    check_eq_result_encoding: assert property (
        @(posedge clk) (a == b) |-> (res == 2'b11)
    );

    // Result 01 only occurs when a is greater than b.
    check_result_01_implies_gt: assert property (
        @(posedge clk) (res == 2'b01) |-> (a > b)
    );

    // Result 10 only occurs when a is less than b.
    check_result_10_implies_lt: assert property (
        @(posedge clk) (res == 2'b10) |-> (a < b)
    );

    // Result 11 only occurs when a equals b.
    check_result_11_implies_eq: assert property (
        @(posedge clk) (res == 2'b11) |-> (a == b)
    );

    // The RTL never drives the unused 00 encoding.
    check_result_never_zero: assert property (
        @(posedge clk) res != 2'b00
    );

endmodule