module dff_sva #(
    parameter WIDTH = 1
) (
    input logic clk,
    input logic rst,
    input logic [WIDTH-1:0] inp,
    input logic [WIDTH-1:0] outp
);

    // A sampled reset cycle drives the output to zero.
    check_reset_drives_zero: assert property (
        @(posedge clk) rst |=> (outp == {WIDTH{1'b0}})
    );

    // With reset low across consecutive cycles, the output captures the prior input.
    check_capture_prev_input_no_reset: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !$past(rst) |-> (outp == $past(inp))
    );

    // The output always matches the previous cycle's reset-or-data decision.
    check_state_matches_prev_cycle_inputs: assert property (
        @(posedge clk) disable iff ($initstate)
        outp == ($past(rst) ? {WIDTH{1'b0}} : $past(inp))
    );

endmodule