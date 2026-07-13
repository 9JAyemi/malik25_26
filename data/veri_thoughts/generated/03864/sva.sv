module anyedge_detection_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [7:0] anyedge,
    input logic [7:0] prev_state,
    input logic [7:0] curr_state,
    input logic [7:0] edge_detect
);

    // curr_state captures the input from the previous clock.
    check_curr_state_samples_input: assert property (
        @(posedge clk)
        !$initstate |-> (curr_state == $past(in))
    );

    // prev_state captures the prior value of curr_state.
    check_prev_state_tracks_curr_state: assert property (
        @(posedge clk)
        !$initstate |-> (prev_state == $past(curr_state))
    );

    // prev_state is the input delayed by two clocks.
    check_prev_state_is_two_cycle_input_delay: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate)) |-> (prev_state == $past(in, 2))
    );

    // edge_detect is the XOR of the two sampled states.
    check_edge_detect_is_xor: assert property (
        @(posedge clk)
        (edge_detect == (prev_state ^ curr_state))
    );

    // anyedge is edge_detect masked by curr_state.
    check_anyedge_matches_masked_xor: assert property (
        @(posedge clk)
        (anyedge == (edge_detect & curr_state))
    );

    // anyedge is high only for 0-to-1 state transitions.
    check_anyedge_is_rise_only: assert property (
        @(posedge clk)
        (anyedge == (~prev_state & curr_state))
    );

    // anyedge bits must always be a subset of curr_state bits.
    check_anyedge_subset_of_curr_state: assert property (
        @(posedge clk)
        ((anyedge & ~curr_state) == 8'h00)
    );

    // anyedge bits must never overlap bits already high in prev_state.
    check_anyedge_excludes_prev_state_high: assert property (
        @(posedge clk)
        ((anyedge & prev_state) == 8'h00)
    );

    // anyedge reflects a sampled rise on the input across the last two clocks.
    check_anyedge_matches_sampled_input_rise: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate)) |-> (anyedge == ($past(in) & ~$past(in, 2)))
    );

endmodule

bind anyedge_detection anyedge_detection_sva anyedge_detection_sva_inst (
    .clk(clk),
    .in(in),
    .anyedge(anyedge),
    .prev_state(prev_state),
    .curr_state(curr_state),
    .edge_detect(edge_detect)
);