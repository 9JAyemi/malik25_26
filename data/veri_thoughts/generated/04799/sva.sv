module comparator_sva (
    input logic clk,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic equal,
    input logic greater_than,
    input logic less_than
);

    // equal must reflect A == B.
    check_equal_function: assert property (
        @(posedge clk) equal == (A == B)
    );

    // greater_than must reflect A > B.
    check_greater_than_function: assert property (
        @(posedge clk) greater_than == (A > B)
    );

    // less_than must reflect A < B.
    check_less_than_function: assert property (
        @(posedge clk) less_than == (A < B)
    );

    // Outputs must be mutually exclusive.
    check_outputs_mutually_exclusive: assert property (
        @(posedge clk) !(equal && greater_than) &&
                       !(equal && less_than) &&
                       !(greater_than && less_than)
    );

    // Exactly one comparison result must be active.
    check_one_result_active: assert property (
        @(posedge clk) equal || greater_than || less_than
    );

    // Stable inputs must keep the outputs stable.
    check_stable_inputs_stable_outputs: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable({equal, greater_than, less_than})
    );

endmodule