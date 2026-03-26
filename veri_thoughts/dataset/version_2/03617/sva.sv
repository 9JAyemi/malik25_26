module addsub_assertions (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] S
);

    // When SUB is high, S must be the 4-bit difference A - B.
    check_subtract_result: assert property (
        @(posedge clk) SUB |-> (S == (A - B))
    );

    // When SUB is low, S must be the 4-bit sum A + B.
    check_add_result: assert property (
        @(posedge clk) !SUB |-> (S == (A + B))
    );

    // If inputs do not change between samples, the output must also remain unchanged.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({A, B, SUB}) |-> $stable(S)
    );

endmodule