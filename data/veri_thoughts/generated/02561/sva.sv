module calculator_sva (
    input logic CLK,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic add,
    input logic sub,
    input logic [7:0] result
);
    // Result matches the combinational ternary equation.
    check_result_matches_equation: assert property (
        @(posedge CLK) result == (add ? (a + b) : (sub ? (a - b) : 8'h00))
    );

    // When add is asserted, result equals a + b (priority over sub).
    check_add_priority: assert property (
        @(posedge CLK) add |-> (result == (a + b))
    );

    // When only sub is asserted, result equals a - b.
    check_sub_when_no_add: assert property (
        @(posedge CLK) (!add && sub) |-> (result == (a - b))
    );

    // When neither add nor sub is asserted, result is zero.
    check_zero_when_no_ops: assert property (
        @(posedge CLK) (!add && !sub) |-> (result == 8'h00)
    );

    // When both add and sub are asserted, add takes precedence (result is a + b).
    check_both_ops_add_wins: assert property (
        @(posedge CLK) (add && sub) |-> (result == (a + b))
    );
endmodule