module calculator_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);

// Addition opcode returns the low byte of a + b.
    check_add_result: assert property (
        @(posedge clk) (op == 2'b00) |-> (result == ((a + b) & 8'hFF))
    );

// Subtraction opcode returns the low byte of a - b.
    check_sub_result: assert property (
        @(posedge clk) (op == 2'b01) |-> (result == ((a - b) & 8'hFF))
    );

// Division by zero returns 0xFF.
    check_div_zero_result: assert property (
        @(posedge clk) (op == 2'b11 && b == 8'h00) |-> (result == 8'hFF)
    );

endmodule
