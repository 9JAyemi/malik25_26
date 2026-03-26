module adder_subtractor_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       subtract,
    input logic [3:0] result
);

    // When subtract is selected, result is A minus B.
    check_subtract_mode: assert property (
        @($global_clock) (subtract === 1'b1) |-> (result === (A - B))
    );

    // When subtract is not selected, result is A plus B.
    check_add_mode: assert property (
        @($global_clock) (subtract !== 1'b1) |-> (result === (A + B))
    );

    // With unchanged inputs, the combinational result stays unchanged.
    check_stateless_output: assert property (
        @($global_clock) ($stable(A) && $stable(B) && $stable(subtract)) |-> $stable(result)
    );

endmodule