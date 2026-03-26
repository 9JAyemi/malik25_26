module arithmetic_operations_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [2:0] ctrl,
    input logic [7:0] out
);

    // ctrl 000 selects bitwise AND.
    check_and_operation: assert property (
        @(posedge clk) (ctrl == 3'b000) |-> (out == (A & B))
    );

    // ctrl 001 selects bitwise OR.
    check_or_operation: assert property (
        @(posedge clk) (ctrl == 3'b001) |-> (out == (A | B))
    );

    // ctrl 010 selects bitwise XOR.
    check_xor_operation: assert property (
        @(posedge clk) (ctrl == 3'b010) |-> (out == (A ^ B))
    );

    // ctrl 011 selects addition.
    check_add_operation: assert property (
        @(posedge clk) (ctrl == 3'b011) |-> (out == (A + B))
    );

    // ctrl 100 selects subtraction.
    check_sub_operation: assert property (
        @(posedge clk) (ctrl == 3'b100) |-> (out == (A - B))
    );

    // ctrl 101 selects multiplication with 8-bit truncation.
    check_mul_operation: assert property (
        @(posedge clk) (ctrl == 3'b101) |-> (out == ((A * B) & 16'h00FF))
    );

    // ctrl 110 selects division when the divisor is non-zero.
    check_div_operation: assert property (
        @(posedge clk) ((ctrl == 3'b110) && (B != 8'h00)) |-> (out == (A / B))
    );

    // ctrl 111 selects modulo when the divisor is non-zero.
    check_mod_operation: assert property (
        @(posedge clk) ((ctrl == 3'b111) && (B != 8'h00)) |-> (out == (A % B))
    );

endmodule