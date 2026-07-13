module MUX_2_1_sva (
    input logic I0,
    input logic I1,
    input logic S,
    input logic O
);

    // No RTL clock or reset; O is updated only by the always @(S) process.

    // After S goes low, O must hold the I0 sample taken at that edge until S changes again.
    check_select_low_holds_sampled_i0_until_next_select_change: assert property (
        @(posedge S or negedge S) !S |=> (O == $past(I0))
    );

    // After S goes high, O must hold the I1 sample taken at that edge until S changes again.
    check_select_high_holds_sampled_i1_until_next_select_change: assert property (
        @(posedge S or negedge S) S |=> (O == $past(I1))
    );

    // When O rises, it must match the currently selected input.
    check_output_rise_matches_selected_input: assert property (
        @(posedge O) (S ? I1 : I0)
    );

    // When O falls, it must match the currently selected input.
    check_output_fall_matches_selected_input: assert property (
        @(negedge O) !(S ? I1 : I0)
    );

endmodule