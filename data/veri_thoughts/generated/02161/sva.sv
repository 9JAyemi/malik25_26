module sourceMod_sva (
    input logic ctrl_clk,
    input logic ctrl_data,
    input logic validData
);
    // If validData is 1, it becomes 0 on the next clock.
    check_toggle_1_to_0: assert property (
        @(posedge ctrl_clk) disable iff ($initstate)
            (validData === 1'b1) |-> ##1 (validData === 1'b0)
    );

    // If validData is 0, it becomes 1 on the next clock.
    check_toggle_0_to_1: assert property (
        @(posedge ctrl_clk) disable iff ($initstate)
            (validData === 1'b0) |-> ##1 (validData === 1'b1)
    );

    // A rise on validData is followed by a fall on the next clock.
    check_rise_followed_by_fall: assert property (
        @(posedge ctrl_clk) disable iff ($initstate)
            $rose(validData) |-> ##1 $fell(validData)
    );

    // A fall on validData is followed by a rise on the next clock.
    check_fall_followed_by_rise: assert property (
        @(posedge ctrl_clk) disable iff ($initstate)
            $fell(validData) |-> ##1 $rose(validData)
    );

    // When known, validData repeats every two clocks.
    check_two_cycle_periodicity: assert property (
        @(posedge ctrl_clk) disable iff ($initstate)
            (((validData===1'b0)||(validData===1'b1)) &&
             (($past(validData,2)===1'b0)||($past(validData,2)===1'b1)))
            |-> (validData == $past(validData,2))
    );

    // When known in consecutive cycles, validData toggles each clock.
    check_toggle_each_cycle_when_known: assert property (
        @(posedge ctrl_clk) disable iff ($initstate)
            (((validData===1'b0)||(validData===1'b1)) &&
             (($past(validData)===1'b0)||($past(validData)===1'b1)))
            |-> (validData != $past(validData))
    );
endmodule