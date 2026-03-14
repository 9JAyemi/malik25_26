module calculator_sva (
    input logic CLK,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    input logic [7:0] result
);
    // When op=00, result must equal A+B (8-bit wrap)
    check_addition: assert property (
        @(posedge CLK) (op == 2'b00) |-> (result == (A + B))
    );

    // When op=01, result must equal A-B (8-bit wrap)
    check_subtraction: assert property (
        @(posedge CLK) (op == 2'b01) |-> (result == (A - B))
    );

    // When op=10, result must equal low 8 bits of A*B
    check_multiplication_low8: assert property (
        @(posedge CLK) (op == 2'b10) |-> (result == (A * B)[7:0])
    );

    // When op=11 and B!=0, result must equal A/B
    check_division_nonzero: assert property (
        @(posedge CLK) (op == 2'b11 && B != 8'd0) |-> (result == (A / B))
    );

    // If inputs are stable, result must remain stable
    check_stable_result_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(op)) |-> $stable(result)
    );

    // If result changes, at least one of A, B, or op must have changed
    check_result_change_implies_input_change: assert property (
        @(posedge CLK) $changed(result) |-> ($changed(A) || $changed(B) || $changed(op))
    );
endmodule