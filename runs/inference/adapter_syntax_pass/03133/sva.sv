module min_max_sva #(
    parameter n = 8
)(
    input logic clk,
    input logic [n-1:0] in,
    input logic [n-1:0] min,
    input logic [n-1:0] max
);

    // min must be the smallest input bit.
    check_min_matches_input: assert property (
        @(posedge clk) min == in[0]
    );

    // max must be the largest input bit.
    check_max_matches_input: assert property (
        @(posedge clk) max == in[0]
    );

    // min must be less than or equal to max.
    check_min_le_max: assert property (
        @(posedge clk) min <= max
    );

    // min must be less than or equal to every input bit.
    check_min_le_all_inputs: assert property (
        @(posedge clk) min <= in
    );

    // max must be greater than or equal to every input bit.
    check_max_ge_all_inputs: assert property (
        @(posedge clk) max >= in
    );

    // min must equal max when the input is constant.
    check_equal_inputs: assert property (
        @(posedge clk) (in == {n{in[0]}}) |-> (min == max)
    );

endmodule