module comparator_8bit_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic equal,
    input logic greater_than,
    input logic less_than
);

    // Equal inputs select only equal.
    check_equal_case: assert property (
        @(posedge clk) (A == B) |-> (equal && !greater_than && !less_than)
    );

    // A greater than B selects only greater_than.
    check_greater_case: assert property (
        @(posedge clk) (A > B) |-> (!equal && greater_than && !less_than)
    );

    // A less than B selects only less_than.
    check_less_case: assert property (
        @(posedge clk) (A < B) |-> (!equal && !greater_than && less_than)
    );

    // equal and greater_than cannot be high together.
    check_equal_greater_mutex: assert property (
        @(posedge clk) !(equal && greater_than)
    );

    // equal and less_than cannot be high together.
    check_equal_less_mutex: assert property (
        @(posedge clk) !(equal && less_than)
    );

    // greater_than and less_than cannot be high together.
    check_greater_less_mutex: assert property (
        @(posedge clk) !(greater_than && less_than)
    );

    // One result output must always be asserted.
    check_result_present: assert property (
        @(posedge clk) (equal || greater_than || less_than)
    );

endmodule