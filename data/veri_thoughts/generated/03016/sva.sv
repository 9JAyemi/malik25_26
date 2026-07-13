module bar_assertions (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [1:0] sel,
    input logic [3:0] result
);

    // When sel is 00, result is the 4-bit sum of a and b.
    check_result_add: assert property (
        @($global_clock) (sel == 2'b00) |-> (result == ((a + b) & 4'hF))
    );

    // When sel is 01, result is the 4-bit value of a + ~b + 1.
    check_result_sub: assert property (
        @($global_clock) (sel == 2'b01) |-> (result == ((a + ~b + 1) & 4'hF))
    );

    // When sel is 10, result is the bitwise AND of a and b.
    check_result_and: assert property (
        @($global_clock) (sel == 2'b10) |-> (result == (a & b))
    );

    // When sel is 11, result is the bitwise OR of a and b.
    check_result_or: assert property (
        @($global_clock) (sel == 2'b11) |-> (result == (a | b))
    );

endmodule