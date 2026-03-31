module bitwise_or_logical_or_not_sva (
    input logic clk,
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [2:0] out_or_bitwise,
    input logic out_or_logical,
    input logic [5:0] out_not
);

// out_or_bitwise must match the bitwise OR of a and b.
    check_or_bitwise_matches_inputs: assert property (
        @(posedge clk) out_or_bitwise == (a | b)
    );

// out_or_logical must match the logical OR of out_or_bitwise.
    check_or_logical_matches_or_bitwise: assert property (
        @(posedge clk) out_or_logical == |out_or_bitwise
    );

// out_not must match the concatenation of the inverted inputs.
    check_not_concat_matches_inputs: assert property (
        @(posedge clk) out_not == {~a, ~b}
    );

// The upper three bits of out_not must be the inverted a values.
    check_not_upper_matches_a: assert property (
        @(posedge clk) out_not[5:3] == ~a
    );

// The lower three bits of out_not must be the inverted b values.
    check_not_lower_matches_b: assert property (
        @(posedge clk) out_not[2:0] == ~b
    );

// A high out_or_logical implies at least one input bit is high.
    check_or_logical_high_implies_any_input_high: assert property (
        @(posedge clk) out_or_logical |-> (|a || |b)
    );

// Any high input bit must drive out_or_logical high.
    check_any_input_high_implies_or_logical_high: assert property (
        @(posedge clk) (|a || |b) |-> out_or_logical
    );

// A low out_or_logical implies all input bits are low.
    check_or_logical_low_implies_all_inputs_low: assert property (
        @(posedge clk) !out_or_logical |-> (!|a && !|b)
    );

// All low input bits must drive out_or_logical low.
    check_all_inputs_low_implies_or_logical_low: assert property (
        @(posedge clk) (!|a && !|b) |-> !out_or_logical
    );

endmodule
