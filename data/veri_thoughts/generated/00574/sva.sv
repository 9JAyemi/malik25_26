module comparator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] C
);

    // When A equals B, output must be 00.
    check_equal_implies_code_00: assert property (
        @(posedge clk) disable iff (1'b0) (A == B) |-> (C == 2'b00)
    );

    // When A greater than B, output must be 01.
    check_greater_implies_code_01: assert property (
        @(posedge clk) disable iff (1'b0) (A > B) |-> (C == 2'b01)
    );

    // When A less than B, output must be 10.
    check_less_implies_code_10: assert property (
        @(posedge clk) disable iff (1'b0) (A < B) |-> (C == 2'b10)
    );

    // Output 00 only occurs when A equals B.
    check_code_00_implies_equal: assert property (
        @(posedge clk) disable iff (1'b0) (C == 2'b00) |-> (A == B)
    );

    // Output 01 only occurs when A greater than B.
    check_code_01_implies_greater: assert property (
        @(posedge clk) disable iff (1'b0) (C == 2'b01) |-> (A > B)
    );

    // Output 10 only occurs when A less than B.
    check_code_10_implies_less: assert property (
        @(posedge clk) disable iff (1'b0) (C == 2'b10) |-> (A < B)
    );

    // Output must never be 11.
    check_output_not_11: assert property (
        @(posedge clk) disable iff (1'b0) (C != 2'b11)
    );

    // When A != B, output must not be 00.
    check_neq_implies_not_00: assert property (
        @(posedge clk) disable iff (1'b0) (A != B) |-> (C != 2'b00)
    );

endmodule