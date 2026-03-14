module debounce_sva (
    input logic clk,
    input logic button,
    input logic button_state,
    input logic button_up,
    input logic button_down,
    input logic current_state,
    input logic previous_state,
    input logic [15:0] debounce_counter
);
    // Clock: clk (posedge). Reset: none in RTL (initial values). Logic: sequential (posedge clk).

    // Debounce counter increments by 1 while below the limit.
    check_counter_increments_until_limit: assert property (
        @(posedge clk) (debounce_counter < 16'd10000) |=> (debounce_counter == $past(debounce_counter) + 16'd1)
    );

    // Debounce counter saturates at the limit once reached.
    check_counter_saturates_at_limit: assert property (
        @(posedge clk) (debounce_counter == 16'd10000) |=> (debounce_counter == 16'd10000)
    );

    // Debounce counter never exceeds the limit.
    check_counter_never_exceeds_limit: assert property (
        @(posedge clk) (debounce_counter <= 16'd10000)
    );

    // current_state samples button with 1-cycle latency.
    check_current_state_samples_button: assert property (
        @(posedge clk) 1'b1 |=> (current_state == $past(button))
    );

    // previous_state equals prior-cycle current_state.
    check_previous_state_tracks_current: assert property (
        @(posedge clk) 1'b1 |=> (previous_state == $past(current_state))
    );

    // button_state is stable until debounce_counter reaches the limit.
    check_button_state_stable_before_limit: assert property (
        @(posedge clk) 1'b1 |=> ((debounce_counter != 16'd10000) |-> $stable(button_state))
    );

    // At/after the limit, button_state follows prior-cycle current_state.
    check_button_state_follows_current_at_limit: assert property (
        @(posedge clk) (debounce_counter == 16'd10000) |=> (button_state == $past(current_state))
    );

    // button_down can only rise if prior cycle had a down event at the limit.
    check_button_down_rise_requires_event: assert property (
        @(posedge clk) $rose(button_down) |-> $past(debounce_counter == 16'd10000) && $past(current_state & ~previous_state)
    );

    // button_up can only rise if prior cycle had an up event at the limit.
    check_button_up_rise_requires_event: assert property (
        @(posedge clk) $rose(button_up) |-> $past(debounce_counter == 16'd10000) && $past((~current_state) & previous_state)
    );

    // A down event at the limit causes button_down to be high next cycle.
    check_button_down_set_on_down_event: assert property (
        @(posedge clk) (debounce_counter == 16'd10000 && current_state && ~previous_state) |=> button_down
    );

    // An up event at the limit causes button_up to be high next cycle.
    check_button_up_set_on_up_event: assert property (
        @(posedge clk) (debounce_counter == 16'd10000 && ~current_state && previous_state) |=> button_up
    );

    // button_up and button_down cannot rise in the same cycle.
    check_button_pulse_rise_mutex: assert property (
        @(posedge clk) !($rose(button_up) && $rose(button_down))
    );

    // button_down never falls (sticky once set).
    check_button_down_never_falls: assert property (
        @(posedge clk) !$fell(button_down)
    );

    // button_up never falls (sticky once set).
    check_button_up_never_falls: assert property (
        @(posedge clk) !$fell(button_up)
    );

endmodule