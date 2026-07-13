module comparator_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] result
);

// Result 00 only occurs when A equals B.
    check_equal_maps_zero: assert property (
        @(posedge clk) (A == B) |-> (result == 2'b00)
    );

// Result 01 only occurs when A is greater than B.
    check_greater_maps_one: assert property (
        @(posedge clk) (A > B) |-> (result == 2'b01)
    );

// Result 10 only occurs when A is less than B.
    check_less_maps_two: assert property (
        @(posedge clk) (A < B) |-> (result == 2'b10)
    );

// Result 11 is never produced by this comparator.
    check_no_three: assert property (
        @(posedge clk) (result != 2'b11)
    );

// Result is always one of the three implemented encodings.
    check_result_legal: assert property (
        @(posedge clk) (result == 2'b00) || (result == 2'b01) || (result == 2'b10)
    );

endmodule
