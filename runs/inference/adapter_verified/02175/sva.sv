module Comparator_sva (
    input logic clk,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [1:0] out
);

// out must be 00 when inputs are equal.
    check_equal_maps_zero: assert property (
        @(posedge clk) (in1 == in2) |-> (out == 2'b00)
    );

// out must be 01 when in1 is greater than in2.
    check_greater_maps_one: assert property (
        @(posedge clk) (in1 > in2) |-> (out == 2'b01)
    );

// out must be 10 when in1 is less than in2.
    check_less_maps_two: assert property (
        @(posedge clk) (in1 < in2) |-> (out == 2'b10)
    );

// out must never be 11.
    check_no_invalid_code: assert property (
        @(posedge clk) (out != 2'b11)
    );

// out must always match the RTL comparison result.
    check_full_functional_equivalence: assert property (
        @(posedge clk) out == ((in1 > in2) ? 2'b01 : ((in1 == in2) ? 2'b00 : 2'b10))
    );

endmodule
