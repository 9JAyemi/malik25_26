module motor_control_sva #(
    parameter int steps_per_rev = 200
) (
    input  logic       step,
    input  logic       dir,
    input  logic       ctrl,
    input  logic [7:0] count,
    input  logic       direction
);
    localparam int HALF = steps_per_rev/2;

    // If previous count != steps_per_rev and != 0xFF, count increments by 1 on each step.
    count_increments_no_overflow: assert property (
        @(posedge step) ($past(count) != steps_per_rev) && ($past(count) != 8'hFF) |-> (count == $past(count) + 8'd1)
    );

    // If previous count == steps_per_rev, count resets to 0 on next step.
    count_resets_at_steps_per_rev: assert property (
        @(posedge step) ($past(count) == steps_per_rev) |-> (count == 8'd0)
    );

    // If previous count == 0xFF and not equal to steps_per_rev, count wraps to 0.
    count_wraps_on_overflow: assert property (
        @(posedge step) ($past(count) == 8'hFF) && ($past(count) != steps_per_rev) |-> (count == 8'd0)
    );

    // If count is 0 now, previous count was steps_per_rev or 0xFF.
    count_zero_has_valid_predecessor: assert property (
        @(posedge step) (count == 8'd0) |-> (($past(count) == steps_per_rev) || ($past(count) == 8'hFF))
    );

    // When dir is 1 at step, direction toggles.
    direction_toggles_when_dir_high: assert property (
        @(posedge step) (dir == 1'b1) |-> (direction == ~$past(direction))
    );

    // When dir is 0 at step, direction holds.
    direction_holds_when_dir_low: assert property (
        @(posedge step) (dir == 1'b0) |-> (direction == $past(direction))
    );

    // Any change in direction requires dir to be 1 at that step.
    direction_change_requires_dir_high: assert property (
        @(posedge step) $changed(direction) |-> (dir == 1'b1)
    );

    // When count equals HALF, ctrl equals direction.
    ctrl_equals_direction_at_half: assert property (
        @(posedge step) (count == HALF) |-> (ctrl == direction)
    );

    // When count does not equal HALF, ctrl equals inverted direction.
    ctrl_equals_inverted_direction_when_not_half: assert property (
        @(posedge step) (count != HALF) |-> (ctrl == ~direction)
    );

    // If ctrl changes, exactly one of direction or (count==HALF) changed.
    ctrl_change_parity_odd: assert property (
        @(posedge step) $changed(ctrl) |-> ($changed(direction) ^ $changed(count == HALF))
    );

    // If ctrl does not change, direction and (count==HALF) either both changed or both held.
    ctrl_stable_parity_even: assert property (
        @(posedge step) !$changed(ctrl) |-> (~($changed(direction) ^ $changed(count == HALF)))
    );

endmodule