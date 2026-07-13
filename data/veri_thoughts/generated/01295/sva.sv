module bitwise_or_twos_complement_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] out
);
    // out equals two's complement of (a | b).
    out_twos_comp_def: assert property (
        @(posedge clk) out == ((~(a | b)) + 4'd1)
    );

    // out plus (a | b) wraps to zero (mod 16).
    sum_with_or_zero: assert property (
        @(posedge clk) (out + (a | b)) == 4'd0
    );

    // out is zero iff both a and b are zero.
    zero_iff_a_b_zero: assert property (
        @(posedge clk) (out == 4'd0) == ((a == 4'd0) && (b == 4'd0))
    );

    // Two's complement of out yields (a | b).
    double_negation_returns_or: assert property (
        @(posedge clk) ((~out) + 4'd1) == (a | b)
    );

    // If inputs are stable, output is stable.
    stable_out_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> $stable(out)
    );

    // If (a | b) is unchanged, out is unchanged.
    stable_out_when_or_unchanged: assert property (
        @(posedge clk) ((a | b) == $past(a | b)) |-> (out == $past(out))
    );

    // If (a | b) is 8, out is also 8 (self-negating).
    or_8_maps_to_out_8: assert property (
        @(posedge clk) ((a | b) == 4'd8) |-> (out == 4'd8)
    );

    // If (a | b) is 15 (all ones), out is 1.
    or_all_ones_maps_to_one: assert property (
        @(posedge clk) ((a | b) == 4'hF) |-> (out == 4'd1)
    );

    // Nonzero (a | b) implies nonzero out.
    nonzero_or_implies_nonzero_out: assert property (
        @(posedge clk) ((a | b) != 4'd0) |-> (out != 4'd0)
    );

    // out changes only if (a | b) changes.
    out_change_implies_or_change: assert property (
        @(posedge clk) (out != $past(out)) |-> ((a | b) != $past(a | b))
    );
endmodule