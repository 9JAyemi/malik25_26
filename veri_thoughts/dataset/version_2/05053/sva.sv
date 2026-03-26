module delay_module_sva (
    input logic       clk,
    input logic       A,
    input logic [3:0] delay_val,
    input logic       X,
    input logic [3:0] counter
);

    // Counter increments every clock.
    check_counter_increments: assert property (
        @(posedge clk) (!$initstate) |-> (counter == ($past(counter) + 4'd1))
    );

    // Counter wraps from 15 back to 0.
    check_counter_wraps: assert property (
        @(posedge clk) (!$initstate && ($past(counter) == 4'hF)) |-> (counter == 4'h0)
    );

    // X captures the prior A when the prior counter matches delay_val.
    check_capture_on_match: assert property (
        @(posedge clk) (!$initstate && ($past(counter) == $past(delay_val))) |-> (X == $past(A))
    );

    // X holds its prior value when the prior counter does not match delay_val.
    check_hold_on_mismatch: assert property (
        @(posedge clk) (!$initstate && ($past(counter) != $past(delay_val))) |-> (X == $past(X))
    );

    // Any X change must be caused by a prior counter match.
    check_x_change_requires_match: assert property (
        @(posedge clk) (!$initstate && (X != $past(X))) |-> ($past(counter) == $past(delay_val))
    );

    // Any X change must update X to the prior A value.
    check_x_change_captures_prior_a: assert property (
        @(posedge clk) (!$initstate && (X != $past(X))) |-> (X == $past(A))
    );

    // A prior match with different data must change X.
    check_match_updates_when_data_differs: assert property (
        @(posedge clk) (!$initstate && ($past(counter) == $past(delay_val)) && ($past(A) != $past(X))) |-> (X != $past(X))
    );

endmodule