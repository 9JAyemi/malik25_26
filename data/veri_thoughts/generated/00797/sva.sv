module Counter_sva (
    input logic Clock,
    input logic Reset,
    input logic Enable,
    input logic [3:0] CountTo,
    input logic [3:0] CountValue,
    input logic CountFinished
);
    ///// Functional relationship between outputs /////
    // CountFinished is high iff CountValue equals CountTo.
    check_countfinished_definition: assert property (
        @(posedge Clock) disable iff (Reset) (CountFinished == (CountValue == CountTo))
    );

    ///// Reset behavior /////
    // After a cycle with Reset high, CountValue becomes 0.
    check_reset_clears_countvalue: assert property (
        @(posedge Clock) disable iff (Reset) $past(Reset) |-> (CountValue == 4'd0)
    );

    // If both Reset and Enable were high last cycle, Reset takes precedence and CountValue is 0.
    check_reset_precedence_over_enable: assert property (
        @(posedge Clock) disable iff (Reset) ($past(Reset) && $past(Enable)) |-> (CountValue == 4'd0)
    );

    ///// Enable and hold behavior /////
    // When not Reset and not Enable, CountValue holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge Clock) disable iff (Reset) ($past(!Reset) && !$past(Enable)) |-> (CountValue == $past(CountValue))
    );

    // When enabled and previous CountValue != CountTo, CountValue increments by 1.
    check_increment_when_enabled_ne_equal: assert property (
        @(posedge Clock) disable iff (Reset)
            ($past(!Reset && Enable) && ($past(CountValue) != $past(CountTo))) |-> (CountValue == ($past(CountValue) + 4'd1))
    );

    // When enabled and previous CountValue == CountTo, CountValue wraps to 0.
    check_wrap_when_enabled_equal: assert property (
        @(posedge Clock) disable iff (Reset)
            ($past(!Reset && Enable) && ($past(CountValue) == $past(CountTo))) |-> (CountValue == 4'd0)
    );

    // A change in CountValue only occurs if prior Reset or Enable were asserted.
    check_changes_imply_enable_or_reset: assert property (
        @(posedge Clock) disable iff (Reset) (CountValue != $past(CountValue)) |-> ($past(Reset) || $past(Enable))
    );

    ///// Combinational stability consistency /////
    // If CountValue and CountTo are stable, CountFinished is stable (pure function).
    check_countfinished_stable_when_inputs_stable: assert property (
        @(posedge Clock) disable iff (Reset) ($stable(CountValue) && $stable(CountTo)) |-> $stable(CountFinished)
    );
endmodule