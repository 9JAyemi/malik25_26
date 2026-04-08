module comparator_4bit_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] result
);

    // Result only uses the three encodings implemented in the RTL.
    check_result_encoding: assert property (
        @(posedge clk)
        (result == 2'b00) || (result == 2'b01) || (result == 2'b10)
    );

    // If A has MSB set and B does not, result indicates A > B.
    check_msb_a_high_b_low: assert property (
        @(posedge clk)
        ((A[3] == 1'b1) && (B[3] == 1'b0)) |-> (result == 2'b01)
    );

    // If B has MSB set and A does not, result indicates A < B.
    check_msb_a_low_b_high: assert property (
        @(posedge clk)
        ((A[3] == 1'b0) && (B[3] == 1'b1)) |-> (result == 2'b10)
    );

    // When A is greater than B, result must indicate greater-than.
    check_a_greater_than_b_maps_to_01: assert property (
        @(posedge clk)
        (A > B) |-> (result == 2'b01)
    );

    // When A is less than B, result must indicate less-than.
    check_a_less_than_b_maps_to_10: assert property (
        @(posedge clk)
        (A < B) |-> (result == 2'b10)
    );

    // When A equals B, result must indicate equality.
    check_a_equal_b_maps_to_00: assert property (
        @(posedge clk)
        (A == B) |-> (result == 2'b00)
    );

    // A greater-than result must correspond to A > B.
    check_result_01_implies_a_greater_than_b: assert property (
        @(posedge clk)
        (result == 2'b01) |-> (A > B)
    );

    // A less-than result must correspond to A < B.
    check_result_10_implies_a_less_than_b: assert property (
        @(posedge clk)
        (result == 2'b10) |-> (A < B)
    );

    // An equality result must correspond to A == B.
    check_result_00_implies_a_equal_b: assert property (
        @(posedge clk)
        (result == 2'b00) |-> (A == B)
    );

endmodule