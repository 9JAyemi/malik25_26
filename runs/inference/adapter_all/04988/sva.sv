module calculator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] add,
    input logic [3:0] sub,
    input logic [3:0] mul,
    input logic [3:0] div
);

    // add must equal the 4-bit sum of A and B
    check_add_result: assert property (
        @($global_clock) add == (A + B)
    );

    // sub must equal the 4-bit difference of A and B
    check_sub_result: assert property (
        @($global_clock) sub == (A - B)
    );

    // mul must equal the low 4 bits of the product of A and B
    check_mul_result: assert property (
        @($global_clock) mul == ((A * B) & 5'h0F)
    );

    // div must equal the quotient when A is divided by B
    check_div_result: assert property (
        @($global_clock) (B != 4'h0) |-> (div == (A / B))
    );

    // division by zero must drive div to zero
    check_div_zero_result: assert property (
        @($global_clock) (B == 4'h0) |-> (div == 4'h0)
    );

endmodule