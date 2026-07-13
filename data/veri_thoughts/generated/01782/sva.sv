module falling_edge_detector_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] in,
    input logic [31:0] out
);

    // Assume reset is asserted in the initial state to make $past well-defined.
    assume_init_reset: assume property (
        @(posedge clk) $initstate |-> reset
    );

    // Synchronous reset drives out to zero on the next clock.
    reset_clears_out_next: assert property (
        @(posedge clk) reset |=> (out == 32'b0)
    );

    // Next out equals previous out AND NOT previous in.
    out_update_from_prev_values: assert property (
        @(posedge clk) disable iff (reset) out == ($past(out) & ~$past(in))
    );

    // No bit of out can transition from 0 to 1.
    out_never_raises_bits: assert property (
        @(posedge clk) disable iff (reset) (out & ~$past(out)) == 32'b0
    );

    // Bits that were 1 in previous in cannot be 1 now in out.
    out_disjoint_from_prev_in: assert property (
        @(posedge clk) disable iff (reset) (out & $past(in)) == 32'b0
    );

    // Only bits with previous in=1 may change (from 1 to 0); others remain unchanged.
    out_changes_only_where_prev_in_one: assert property (
        @(posedge clk) disable iff (reset) ((out ^ $past(out)) & ~$past(in)) == 32'b0
    );

    // If previous in was all zeros, out holds its value.
    out_preserved_when_prev_in_zero: assert property (
        @(posedge clk) disable iff (reset) ($past(in) == 32'b0) |-> (out == $past(out))
    );

    // If previous in was all ones, out becomes all zeros.
    out_zero_when_prev_in_all_ones: assert property (
        @(posedge clk) disable iff (reset) ($past(in) == 32'hFFFF_FFFF) |-> (out == 32'b0)
    );

    // If previous out was zero, out remains zero.
    out_zero_when_prev_out_zero: assert property (
        @(posedge clk) disable iff (reset) ($past(out) == 32'b0) |-> (out == 32'b0)
    );

endmodule