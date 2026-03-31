module comparator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic greater,
    input logic less
);

// greater must reflect A > B.
    check_greater_definition: assert property (
        @(posedge clk) greater == (A > B)
    );

// less must reflect A < B.
    check_less_definition: assert property (
        @(posedge clk) less == (A < B)
    );

// Exactly one of greater or less must be HIGH.
    check_outputs_mutex: assert property (
        @(posedge clk) (greater ^ less)
    );

// When A equals B, both outputs must be LOW.
    check_equal_inputs_zero_outputs: assert property (
        @(posedge clk) (A == B) |-> (!greater && !less)
    );

// When A is greater than B, only greater can be HIGH.
    check_greater_high_when_a_gt_b: assert property (
        @(posedge clk) (A > B) |-> (greater && !less)
    );

// When A is less than B, only less can be HIGH.
    check_less_high_when_a_lt_b: assert property (
        @(posedge clk) (A < B) |-> (!greater && less)
    );

endmodule
