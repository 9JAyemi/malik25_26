module top_module_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic        out
);

// Output equals AND of in[15] and in[0].
    check_out_matches_and: assert property (
        @(posedge clk) out == (in[15] & in[0])
    );

// If in[15] is 0, out must be 0.
    check_out_zero_when_msb_zero: assert property (
        @(posedge clk) !in[15] |-> !out
    );

// If in[0] is 0, out must be 0.
    check_out_zero_when_lsb_zero: assert property (
        @(posedge clk) !in[0] |-> !out
    );

// If both in[15] and in[0] are 1, out must be 1.
    check_out_one_when_both_ones: assert property (
        @(posedge clk) (in[15] && in[0]) |-> out
    );

// If out is 1, then both in[15] and in[0] must be 1.
    check_out_one_implies_inputs_one: assert property (
        @(posedge clk) out |-> (in[15] && in[0])
    );

endmodule
