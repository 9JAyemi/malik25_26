module three_input_or_assertions (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic out
);

    // External sampling clock; DUT has no native clock or reset and is combinational.

    // out must match the implemented 3-of-4 OR expression.
    check_out_matches_expression: assert property (
        @(posedge clk)
        out == ((in1 & in2 & in3) |
                (in1 & in2 & in4) |
                (in1 & in3 & in4) |
                (in2 & in3 & in4))
    );

    // in1, in2, and in3 high must force out high.
    check_triplet_123_sets_out: assert property (
        @(posedge clk)
        (in1 & in2 & in3) |-> out
    );

    // in1, in2, and in4 high must force out high.
    check_triplet_124_sets_out: assert property (
        @(posedge clk)
        (in1 & in2 & in4) |-> out
    );

    // in1, in3, and in4 high must force out high.
    check_triplet_134_sets_out: assert property (
        @(posedge clk)
        (in1 & in3 & in4) |-> out
    );

    // in2, in3, and in4 high must force out high.
    check_triplet_234_sets_out: assert property (
        @(posedge clk)
        (in2 & in3 & in4) |-> out
    );

    // If no three-input combination is high, out must be low.
    check_no_triplet_means_out_low: assert property (
        @(posedge clk)
        !((in1 & in2 & in3) |
          (in1 & in2 & in4) |
          (in1 & in3 & in4) |
          (in2 & in3 & in4)) |-> !out
    );

endmodule