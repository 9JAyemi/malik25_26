module bitwise_op_sva (
    input logic       clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [2:0] ctrl,
    input logic [7:0] out
);

    // Output always matches the selected case expression.
    check_output_function: assert property (
        @(posedge clk)
        out === ((ctrl === 3'b000) ? (A & B) :
                 (ctrl === 3'b001) ? (A | B) :
                 (ctrl === 3'b010) ? (A ^ B) :
                                     8'h00)
    );

    // ctrl 000 selects the bitwise AND result.
    check_and_operation: assert property (
        @(posedge clk)
        (ctrl === 3'b000) |-> (out === (A & B))
    );

    // ctrl 001 selects the bitwise OR result.
    check_or_operation: assert property (
        @(posedge clk)
        (ctrl === 3'b001) |-> (out === (A | B))
    );

    // ctrl 010 selects the bitwise XOR result.
    check_xor_operation: assert property (
        @(posedge clk)
        (ctrl === 3'b010) |-> (out === (A ^ B))
    );

    // All other ctrl values drive the default zero output.
    check_default_zero: assert property (
        @(posedge clk)
        (ctrl !== 3'b000 && ctrl !== 3'b001 && ctrl !== 3'b010) |-> (out === 8'h00)
    );

endmodule