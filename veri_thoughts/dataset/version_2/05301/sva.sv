module Comparator_assertions (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] O
);

    localparam logic [2:0] CMP_LT = 3'b000;
    localparam logic [2:0] CMP_EQ = 3'b001;
    localparam logic [2:0] CMP_GT = 3'b010;

    // When A is less than B, O must indicate less-than.
    check_less_than_output: assert property (
        @(posedge clk) (A < B) |-> (O == CMP_LT)
    );

    // When A equals B, O must indicate equality.
    check_equal_output: assert property (
        @(posedge clk) (A == B) |-> (O == CMP_EQ)
    );

    // When A is greater than B, O must indicate greater-than.
    check_greater_than_output: assert property (
        @(posedge clk) (A > B) |-> (O == CMP_GT)
    );

    // The less-than code must only occur when A is less than B.
    check_less_than_code_meaning: assert property (
        @(posedge clk) (O == CMP_LT) |-> (A < B)
    );

    // The equality code must only occur when A equals B.
    check_equal_code_meaning: assert property (
        @(posedge clk) (O == CMP_EQ) |-> (A == B)
    );

    // The greater-than code must only occur when A is greater than B.
    check_greater_than_code_meaning: assert property (
        @(posedge clk) (O == CMP_GT) |-> (A > B)
    );

    // O must always be one of the three implemented encodings.
    check_output_encoding_legal: assert property (
        @(posedge clk) (O == CMP_LT) || (O == CMP_EQ) || (O == CMP_GT)
    );

    // The MSB of O is always zero in all implemented encodings.
    check_output_msb_low: assert property (
        @(posedge clk) O[2] == 1'b0
    );

endmodule