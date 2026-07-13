module bitwise_and_sva (
    input logic clk,
    input logic [3:0] X,
    input logic [3:0] Y,
    input logic [3:0] result,
    input logic greater_than_or_equal_to_5
);

    // result must equal the bitwise AND of X and Y.
    check_result_matches_bitwise_and: assert property (
        @(posedge clk) result == (X & Y)
    );

    // The flag must reflect whether result is at least 5.
    check_flag_matches_result_threshold: assert property (
        @(posedge clk) greater_than_or_equal_to_5 == (result >= 4'd5)
    );

    // A high flag implies the result is 5 or greater.
    check_flag_high_implies_result_ge_5: assert property (
        @(posedge clk) greater_than_or_equal_to_5 |-> (result >= 4'd5)
    );

    // A low flag implies the result is less than 5.
    check_flag_low_implies_result_lt_5: assert property (
        @(posedge clk) !greater_than_or_equal_to_5 |-> (result < 4'd5)
    );

    // The flag must also match the threshold of the ANDed inputs directly.
    check_flag_matches_and_threshold: assert property (
        @(posedge clk) greater_than_or_equal_to_5 == ((X & Y) >= 4'd5)
    );

endmodule