module comparator_sva (
    input logic clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [1:0] result
);

// Result must be 00 when inputs are equal.
    check_equal_maps_zero: assert property (
        @(posedge clk) (in0 == in1) |-> (result == 2'b00)
    );

// Result must be 01 when in0 is greater than in1.
    check_greater_maps_one: assert property (
        @(posedge clk) (in0 > in1) |-> (result == 2'b01)
    );

// Result must be 10 when in0 is less than in1.
    check_less_maps_two: assert property (
        @(posedge clk) (in0 < in1) |-> (result == 2'b10)
    );

// Result must never be 11.
    check_result_never_three: assert property (
        @(posedge clk) (result != 2'b11)
    );

endmodule
