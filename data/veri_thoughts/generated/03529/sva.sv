module ohr_reg0_sva #(parameter int DW = 1) (
    input logic          nreset,
    input logic          clk,
    input logic [DW-1:0] in,
    input logic [DW-1:0] out
);

    // Active-low reset drives the output to zero.
    check_reset_clears_output: assert property (
        @(negedge clk) !nreset |-> (out == '0)
    );

    // The first falling edge after reset release still sees a zero output.
    check_release_edge_output_zero: assert property (
        @(negedge clk) (!nreset ##1 nreset) |-> (out == '0)
    );

    // Each enabled falling edge makes out match the input from the prior falling edge.
    check_output_tracks_prior_input: assert property (
        @(negedge clk) disable iff (!nreset) 1'b1 |=> (out == $past(in))
    );

endmodule