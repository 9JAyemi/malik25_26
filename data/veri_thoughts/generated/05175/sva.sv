module adder_subtractor_sva(
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] Y
);

    // When SUB is 0, Y must equal the 4-bit sum of A and B.
    check_addition_mode_result: assert property (
        @(posedge clk) (SUB === 1'b0) |-> (Y === (A + B))
    );

    // When SUB is not 0, the else branch must drive Y with A - B.
    check_subtraction_mode_result: assert property (
        @(posedge clk) (SUB !== 1'b0) |-> (Y === (A - B))
    );

    // If A, B, and SUB are unchanged, Y must also remain unchanged.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) $stable({A, B, SUB}) |-> $stable(Y)
    );

endmodule