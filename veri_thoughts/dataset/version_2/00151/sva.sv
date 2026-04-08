module bus_hold_sva #(
    parameter n = 8
) (
    input  logic [n-1:0] bus_in,
    input  logic         clk,
    input  logic         reset,
    input  logic [n-1:0] bus_out
);

    // Reset forces the output to zero on the sampled cycle.
    check_reset_forces_zero: assert property (
        @(posedge clk) reset |-> (bus_out == '0)
    );

    // A sampled reset leaves the output at zero on the following cycle.
    check_reset_clears_output_next_cycle: assert property (
        @(posedge clk) reset |=> (bus_out == '0)
    );

    // In consecutive non-reset cycles, the output reflects the prior input sample.
    check_output_tracks_previous_input: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (bus_out == $past(bus_in))
    );

endmodule