module simple_calculator_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] opcode,
    input logic [7:0] result
);
    ///// Operation selection semantics /////
    // When opcode==00, result is low 8 bits of A+B.
    check_add_result_matches_opcode: assert property (
        @(posedge clk) (opcode == 2'b00) |-> (result == (A + B)[7:0])
    );

    // When opcode==01, result is low 8 bits of A-B.
    check_sub_result_matches_opcode: assert property (
        @(posedge clk) (opcode == 2'b01) |-> (result == (A - B)[7:0])
    );

    // When opcode==10, result is low 8 bits of A*B.
    check_mul_result_matches_opcode: assert property (
        @(posedge clk) (opcode == 2'b10) |-> (result == (A * B)[7:0])
    );

    // When opcode==11 and B!=0, result is A/B (8-bit quotient).
    check_div_result_matches_opcode_nonzero: assert property (
        @(posedge clk) (opcode == 2'b11 && (B != 8'd0)) |-> (result == (A / B))
    );

    ///// Functional determinism /////
    // If A,B,opcode are unchanged from last cycle, result must be unchanged.
    check_stable_result_when_inputs_stable: assert property (
        @(posedge clk) (A == $past(A) && B == $past(B) && opcode == $past(opcode)) |-> (result == $past(result))
    );

    // If result changed from last cycle, at least one of A,B,opcode changed.
    check_result_change_implies_input_change: assert property (
        @(posedge clk) (result != $past(result)) |-> ((A != $past(A)) || (B != $past(B)) || (opcode != $past(opcode)))
    );

    ///// Algebraic identities implied by operations /////
    // For opcode==00, adding zero leaves A unchanged.
    check_add_by_zero_identity: assert property (
        @(posedge clk) (opcode == 2'b00 && B == 8'd0) |-> (result == A)
    );

    // For opcode==01, subtracting zero leaves A unchanged.
    check_sub_by_zero_identity: assert property (
        @(posedge clk) (opcode == 2'b01 && B == 8'd0) |-> (result == A)
    );

    // For opcode==10, multiplying by zero yields zero.
    check_mul_by_zero_identity: assert property (
        @(posedge clk) (opcode == 2'b10 && (A == 8'd0 || B == 8'd0)) |-> (result == 8'd0)
    );

    // For opcode==11 and B==1, division yields A.
    check_div_by_one_identity: assert property (
        @(posedge clk) (opcode == 2'b11 && B == 8'd1) |-> (result == A)
    );
endmodule