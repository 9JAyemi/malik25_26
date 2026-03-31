module rising_edge_detector_sva (
    input logic        clk,
    input logic        reset,
    input logic [31:0] in,
    input logic [31:0] out,
    input logic [31:0] prev_state
);

    // Reset clears both internal state and the output.
    check_reset_clears_state: assert property (
        @(posedge clk) reset |=> (prev_state == 32'h00000000 && out == 32'h00000000)
    );

    // prev_state captures the input from the previous cycle.
    check_prev_state_captures_input: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (prev_state == $past(in))
    );

    // out is the previous-cycle input ANDed with the inverted previous-cycle state.
    check_out_matches_registered_delta: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (out == ($past(in) & ~$past(prev_state)))
    );

    // A zero previous-cycle state makes out equal the previous-cycle input.
    check_zero_prev_state_passes_input: assert property (
        @(posedge clk) disable iff (reset)
        ($past(prev_state) == 32'h00000000) |=> (out == $past(in))
    );

    // A zero previous-cycle input makes out equal the inverted previous-cycle state.
    check_zero_input_inverts_prev_state: assert property (
        @(posedge clk) disable iff (reset)
        ($past(in) == 32'h00000000) |=> (out == ~$past(prev_state))
    );

    // Equal previous-cycle input and state make out zero.
    check_equal_input_and_state_clear_out: assert property (
        @(posedge clk) disable iff (reset)
        ($past(in) == $past(prev_state)) |=> (out == 32'h00000000)
    );

    // A zero output implies the previous-cycle input was zero or the previous-cycle state was all ones.
    check_zero_out_implies_zero_input_or_all_ones_state: assert property (
        @(posedge clk) disable iff (reset)
        (out == 32'h00000000) |=> (($past(in) == 32'h00000000) || ($past(prev_state) == 32'hFFFFFFFF))
    );

    // A zero output also implies the previous-cycle state was not all zeros.
    check_zero_out_implies_nonzero_prev_state: assert property (
        @(posedge clk) disable iff (reset)
        (out == 32'h00000000) |=> ($past(prev_state) != 32'h00000000)
    );

    // A zero output also implies the previous-cycle input was not all ones.
    check_zero_out_implies_nonallones_input: assert property (
        @(posedge clk) disable iff (reset)
        (out == 32'h00000000) |=> ($past(in) != 32'hFFFFFFFF)
    );

endmodule

bind rising_edge_detector rising_edge_detector_sva rising_edge_detector_sva_i (
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(out),
    .prev_state(prev_state)
);