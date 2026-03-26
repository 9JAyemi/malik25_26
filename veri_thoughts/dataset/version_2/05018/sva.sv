module bitwise_operations_sva(
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [2:0] op,
    input logic [7:0] result
);

    // External sampling clock; the RTL is combinational and has no reset.

    // op 000 selects bitwise AND.
    check_and_result: assert property (
        @(posedge clk) (op == 3'b000) |-> (result == (a & b))
    );

    // op 001 selects bitwise OR.
    check_or_result: assert property (
        @(posedge clk) (op == 3'b001) |-> (result == (a | b))
    );

    // op 010 selects bitwise XOR.
    check_xor_result: assert property (
        @(posedge clk) (op == 3'b010) |-> (result == (a ^ b))
    );

    // op 011 selects addition.
    check_add_result: assert property (
        @(posedge clk) (op == 3'b011) |-> (result == (a + b))
    );

    // op 100 selects subtraction.
    check_sub_result: assert property (
        @(posedge clk) (op == 3'b100) |-> (result == (a - b))
    );

    // Unsupported op values drive zero.
    check_default_result: assert property (
        @(posedge clk) ((op == 3'b101) || (op == 3'b110) || (op == 3'b111)) |-> (result == 8'b0)
    );

endmodule