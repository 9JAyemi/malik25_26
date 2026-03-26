module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [31:0] in,
    input logic [31:0] out,
    input logic [31:0] trans_out,
    input logic [31:0] shift_out
);

    // Reset clears the sequential outputs on the next clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        reset |=> (trans_out == 32'h00000000 && shift_out == 32'h00000000 && out == 32'h00000000)
    );

    // The top-level output is the OR of the two internal paths.
    check_or_output_function: assert property (
        @(posedge clk) disable iff (reset)
        out == (trans_out | shift_out)
    );

    // The shift-register output matches the prior transition-detector output.
    check_shift_out_tracks_prev_trans_out: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) |-> (shift_out == $past(trans_out))
    );

    // The transition detector accumulates prior-cycle 1->0 transitions on in.
    check_trans_out_update: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) && $past(!reset, 2)) |-> (trans_out == ($past(trans_out) | ($past(in, 2) & ~$past(in))))
    );

    // Once set, transition-detector bits do not clear until reset.
    check_trans_out_monotonic: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) |-> (($past(trans_out) & ~trans_out) == 32'h00000000)
    );

    // Any prior-cycle falling input bit must be reflected in trans_out.
    check_falling_bits_captured: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) && $past(!reset, 2)) |-> ((trans_out & ($past(in, 2) & ~$past(in))) == ($past(in, 2) & ~$past(in)))
    );

    // After a non-reset cycle, the OR stage adds no bits beyond trans_out.
    check_out_matches_trans_out: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) |-> (out == trans_out)
    );

endmodule

bind top_module top_module_sva top_module_sva_inst (
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(out),
    .trans_out(trans_out),
    .shift_out(shift_out)
);