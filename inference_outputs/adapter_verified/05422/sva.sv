module calculator_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    input logic [7:0] result
);

// Addition mode returns the 8-bit sum of A and B.
    check_add_result: assert property (
        @(posedge clk) (op == 2'b00) |-> (result == (A + B))
    );

// Subtraction mode returns the 8-bit difference of A and B.
    check_sub_result: assert property (
        @(posedge clk) (op == 2'b01) |-> (result == (A - B))
    );

// Division by zero forces the result to zero.
    check_div_zero_result: assert property (
        @(posedge clk) (op == 2'b11 && B == 8'h00) |-> (result == 8'h00)
    );

// Division by one passes A through unchanged.
    check_div_one_result: assert property (
        @(posedge clk) (op == 2'b11 && B == 8'h01) |-> (result == A)
    );

// Division by eight shifts A three bits to the right.
    check_div_eight_result: assert property (
        @(posedge clk) (op == 2'b11 && B == 8'h08) |-> (result == (A >> 3))
    );

// Division by 16 returns zero when A is less than 16.
    check_div_sixteen_result: assert property (
        @(posedge clk) (op == 2'b11 && B == 8'h10 && A < 8'h10) |-> (result == 8'h00)
    );

// Division by 16 returns one when A is 16 or greater.
    check_div_sixteen_nonzero_result: assert property (
        @(posedge clk) (op == 2'b11 && B == 8'h10 && A >= 8'h10) |-> (result == 8'h01)
    );

endmodule
