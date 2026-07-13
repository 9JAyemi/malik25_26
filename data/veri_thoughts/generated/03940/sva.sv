module calculator_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] opcode,
    input logic [3:0] result
);

    // Combinational RTL; clk is a sampling clock for formal and there is no reset.

    // Opcode 00 selects 4-bit wrapped addition.
    check_add_result: assert property (
        @(posedge clk) (opcode == 2'b00) |-> (result == ((A + B) & 4'hF))
    );

    // Opcode 01 selects 4-bit wrapped subtraction.
    check_sub_result: assert property (
        @(posedge clk) (opcode == 2'b01) |-> (result == ((A - B) & 4'hF))
    );

    // Opcode 10 selects the low 4 bits of multiplication.
    check_mul_result: assert property (
        @(posedge clk) (opcode == 2'b10) |-> (result == ((A * B) & 4'hF))
    );

    // Opcode 11 selects division when the divisor is nonzero.
    check_div_result_nonzero: assert property (
        @(posedge clk) (opcode == 2'b11 && B != 4'b0000) |-> (result == (A / B))
    );

endmodule