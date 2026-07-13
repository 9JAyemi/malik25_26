module two_bit_comparator_sva (
    input logic clk,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic [1:0] C
);

// C must be 00 when A equals B.
    check_equal_maps_zero: assert property (
        @(posedge clk) (A == B) |-> (C == 2'b00)
    );

// C must be 01 when A is greater than B.
    check_greater_maps_one: assert property (
        @(posedge clk) (A > B) |-> (C == 2'b01)
    );

// C must be 10 when A is less than B.
    check_less_maps_two: assert property (
        @(posedge clk) (A < B) |-> (C == 2'b10)
    );

// C must never be 11.
    check_no_invalid_code: assert property (
        @(posedge clk) (C != 2'b11)
    );

// C must always match the RTL comparison result.
    check_functional_equivalence: assert property (
        @(posedge clk) C == (A == B ? 2'b00 : (A > B ? 2'b01 : 2'b10))
    );

endmodule
