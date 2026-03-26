module calculator_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [2:0] op,
    input logic [7:0] Z
);

    // No explicit clock or reset exists in the RTL; sample on the global formal clock.
    // DUT behavior is purely combinational: A, B, and op fully determine Z.

    // Z must match the full case-based calculator function.
    check_functional_case_mapping: assert property (
        @($global_clock)
        Z == ((op == 3'b000) ? (A + B) :
              (op == 3'b001) ? (A - B) :
              (op == 3'b010) ? ((A * B) & 8'hFF) :
              (op == 3'b011) ? ((B == 8'h00) ? 8'h00 : (A / B)) :
                               8'h00)
    );

    // Addition opcode drives Z to A plus B.
    check_addition_result: assert property (
        @($global_clock) (op == 3'b000) |-> (Z == (A + B))
    );

    // Subtraction opcode drives Z to A minus B.
    check_subtraction_result: assert property (
        @($global_clock) (op == 3'b001) |-> (Z == (A - B))
    );

    // Multiplication opcode drives Z to the low 8 bits of the product.
    check_multiplication_result: assert property (
        @($global_clock) (op == 3'b010) |-> (Z == ((A * B) & 8'hFF))
    );

    // Division by zero returns zero.
    check_divide_by_zero_result: assert property (
        @($global_clock) ((op == 3'b011) && (B == 8'h00)) |-> (Z == 8'h00)
    );

    // Division with nonzero divisor returns the quotient.
    check_division_result: assert property (
        @($global_clock) ((op == 3'b011) && (B != 8'h00)) |-> (Z == (A / B))
    );

    // Unsupported opcodes drive zero.
    check_invalid_opcode_result: assert property (
        @($global_clock) (op[2] == 1'b1) |-> (Z == 8'h00)
    );

endmodule