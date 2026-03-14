module exu_eclcomp8_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic result
);
    // Result equals AND-reduction of bitwise XOR of a and b.
    check_result_equals_andxor: assert property (
        @(posedge clk) result == (&(a ^ b))
    );

    // If b is bitwise complement of a, result must be 1.
    check_complement_implies_result_high: assert property (
        @(posedge clk) (b == ~a) |-> (result == 1'b1)
    );

    // If MSB bits are equal, result must be 0.
    check_zero_if_bit_equal_7: assert property (
        @(posedge clk) (a[7] == b[7]) |-> (result == 1'b0)
    );

    // If bit 6 is equal, result must be 0.
    check_zero_if_bit_equal_6: assert property (
        @(posedge clk) (a[6] == b[6]) |-> (result == 1'b0)
    );

    // If bit 5 is equal, result must be 0.
    check_zero_if_bit_equal_5: assert property (
        @(posedge clk) (a[5] == b[5]) |-> (result == 1'b0)
    );

    // If bit 4 is equal, result must be 0.
    check_zero_if_bit_equal_4: assert property (
        @(posedge clk) (a[4] == b[4]) |-> (result == 1'b0)
    );

    // If bit 3 is equal, result must be 0.
    check_zero_if_bit_equal_3: assert property (
        @(posedge clk) (a[3] == b[3]) |-> (result == 1'b0)
    );

    // If bit 2 is equal, result must be 0.
    check_zero_if_bit_equal_2: assert property (
        @(posedge clk) (a[2] == b[2]) |-> (result == 1'b0)
    );

    // If bit 1 is equal, result must be 0.
    check_zero_if_bit_equal_1: assert property (
        @(posedge clk) (a[1] == b[1]) |-> (result == 1'b0)
    );

    // If LSB bits are equal, result must be 0.
    check_zero_if_bit_equal_0: assert property (
        @(posedge clk) (a[0] == b[0]) |-> (result == 1'b0)
    );
endmodule