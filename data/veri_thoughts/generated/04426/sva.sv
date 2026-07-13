module binary_counter_sva(
    input logic       clk,
    input logic       rst,
    input logic       en,
    input logic [3:0] count
);

    // A reset in the previous cycle forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(rst) |-> (count == 4'b0000)
    );

    // When enabled outside reset, count increments by one.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(!rst && en) |-> (count == ($past(count) + 4'd1))
    );

    // When disabled outside reset, count holds its value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(!rst && !en) |-> (count == $past(count))
    );

    // Any count change must be caused by a prior enable or reset.
    check_count_change_has_valid_cause: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (count != $past(count)) |-> ($past(en) || $past(rst))
    );

    // Incrementing from the maximum value rolls over to zero.
    check_count_rollover_from_max: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        ($past(!rst && en) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule