module custom_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic Y
);

    // Y equals A1 & A2 & A3 & ~B1 on A1 rising edge.
    check_y_eq_func_on_A1: assert property (
        @(posedge A1) Y == (A1 & A2 & A3 & ~B1)
    );

    // Y equals A1 & A2 & A3 & ~B1 on A2 rising edge.
    check_y_eq_func_on_A2: assert property (
        @(posedge A2) Y == (A1 & A2 & A3 & ~B1)
    );

    // Y equals A1 & A2 & A3 & ~B1 on A3 rising edge.
    check_y_eq_func_on_A3: assert property (
        @(posedge A3) Y == (A1 & A2 & A3 & ~B1)
    );

    // Y equals A1 & A2 & A3 & ~B1 on B1 rising edge.
    check_y_eq_func_on_B1: assert property (
        @(posedge B1) Y == (A1 & A2 & A3 & ~B1)
    );

    // If B1 is HIGH, Y must be LOW.
    check_y_low_when_B1_high: assert property (
        @(posedge B1) (B1 == 1'b1) |-> (Y == 1'b0)
    );

    // When Y rises, inputs must satisfy the AND condition.
    check_inputs_when_y_rises: assert property (
        @(posedge Y) (A1 & A2 & A3 & ~B1)
    );

endmodule