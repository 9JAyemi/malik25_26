module shift_and_or_sva (
    input logic clk,
    input logic [31:0] in,
    input logic out,
    input logic [63:0] d_reg
);
    // Clock: clk (posedge). No reset present.
    // Mixed logic: sequential d_reg update; combinational out from d_reg.
    // Behavior: d_reg <= {d_reg[31:0], in[0] ? in : 32'b0}; out == |d_reg[39:0] == in[0] | $past(in[0]).

    ///// Output behavior /////
    // out equals OR of current and previous in[0].
    check_out_depends_on_in0_two_cycles: assert property (
        @(posedge clk) $past(1'b1) |-> (out == (in[0] | $past(in[0])))
    );

    // If current in[0] is HIGH, out must be HIGH in the same cycle.
    check_out_high_when_curr_in0_high: assert property (
        @(posedge clk) in[0] |-> (out == 1'b1)
    );

    // If previous in[0] was HIGH, out must be HIGH this cycle.
    check_out_high_when_prev_in0_high: assert property (
        @(posedge clk) ($past(1'b1) && $past(in[0])) |-> (out == 1'b1)
    );

    // If current and previous in[0] are both LOW, out must be LOW.
    check_out_low_when_two_consec_in0_low: assert property (
        @(posedge clk) ($past(1'b1) && !in[0] && !$past(in[0])) |-> (out == 1'b0)
    );

    // If out is LOW, then both current and previous in[0] are LOW.
    check_out_low_implies_two_consec_in0_low: assert property (
        @(posedge clk) ($past(1'b1) && (out == 1'b0)) |-> (!in[0] && !$past(in[0]))
    );

    // If previous out was LOW, out now equals current in[0].
    check_out_equals_in0_when_prev_out_low: assert property (
        @(posedge clk) ($past(1'b1) && ($past(out) == 1'b0)) |-> (out == in[0])
    );

    ///// Register update behavior /////
    // d_reg next state matches {past lower 32, (in[0]? in : 0)}.
    check_dreg_next_state_update: assert property (
        @(posedge clk) $past(1'b1) |-> (d_reg == { $past(d_reg[31:0]), (in[0] ? in : 32'b0) })
    );

    // Upper 32 bits shift from the previous lower 32 bits.
    check_dreg_upper32_shift: assert property (
        @(posedge clk) $past(1'b1) |-> (d_reg[63:32] == $past(d_reg[31:0]))
    );

    // When in[0] is HIGH, lower 32 bits load 'in'.
    check_dreg_lower32_load_on_in0_high: assert property (
        @(posedge clk) in[0] |-> (d_reg[31:0] == in)
    );

    // When in[0] is LOW, lower 32 bits clear to zero.
    check_dreg_lower32_clear_on_in0_low: assert property (
        @(posedge clk) !in[0] |-> (d_reg[31:0] == 32'b0)
    );

    ///// Combinational mapping /////
    // out equals OR-reduction of d_reg[39:0].
    check_out_equals_or_of_dreg_lower40: assert property (
        @(posedge clk) (out == (|d_reg[39:0]))
    );

endmodule