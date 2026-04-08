module mux_2_1_syncreset_sva (
    input logic        clk,
    input logic        rst,
    input logic        sel,
    input logic [31:0] in1,
    input logic [31:0] in2,
    input logic [31:0] out
);

    // A reset sampled on the previous clock clears the registered output.
    check_prev_reset_clears_out: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(rst) === 1'b1) |-> (out === 32'd0)
    );

    // When previously not in reset and sel was high, out captures in1.
    check_prev_sel_high_captures_in1: assert property (
        @(posedge clk) disable iff ($initstate)
        (($past(rst) !== 1'b1) && ($past(sel) === 1'b1)) |-> (out === $past(in1))
    );

    // When previously not in reset and sel was not high, out captures in2.
    check_prev_sel_not_high_captures_in2: assert property (
        @(posedge clk) disable iff ($initstate)
        (($past(rst) !== 1'b1) && ($past(sel) !== 1'b1)) |-> (out === $past(in2))
    );

    // The output always matches the previous cycle's reset and mux decision.
    check_registered_mux_behavior: assert property (
        @(posedge clk) disable iff ($initstate)
        (($past(rst) === 1'b1) ?
            (out === 32'd0) :
            (($past(sel) === 1'b1) ? (out === $past(in1)) : (out === $past(in2)))
        )
    );

endmodule