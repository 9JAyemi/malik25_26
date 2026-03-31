module min_max_sva (
    input logic clk,
    input logic [n-1:0] in,
    input logic [n-1:0] min,
    input logic [n-1:0] max
);

// min must equal the minimum input value.
    check_min_matches_input: assert property (
        @(posedge clk) min == minmax(in, 1'b0)
    );

// max must equal the maximum input value.
    check_max_matches_input: assert property (
        @(posedge clk) max == minmax(in, 1'b1)
    );

// min and max must differ when the input set is not a singleton.
    check_min_max_different_when_not_singleton: assert property (
        @(posedge clk) (|in ^ in[0]) |-> (min != max)
    );

// Equal input values must produce equal min and max.
    check_equal_inputs_produce_equal_outputs: assert property (
        @(posedge clk) (|in ^ in[0]) |-> (min == max)
    );

// min must be less than or equal to max.
    check_min_le_max: assert property (
        @(posedge clk) min <= max
    );

// min must equal the first input value when the input set is a singleton.
    check_singleton_min: assert property (
        @(posedge clk) (|in ^ in[0]) |-> (min == in[0])
    );

// max must equal the first input value when the input set is a singleton.
    check_singleton_max: assert property (
        @(posedge clk) (|in ^ in[0]) |-> (max == in[0])
    );

endmodule
