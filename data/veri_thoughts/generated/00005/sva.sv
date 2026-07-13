module resultcounter_sva (
    input logic [1:0] resultID,
    input logic       newresult,
    input logic [1:0] done,
    input logic       reset,
    input logic       globalreset,
    input logic       clk,
    input logic [3:0] count,
    input logic [1:0] curr
);

    // done is zero whenever the counter is nonzero.
    check_done_zero_when_count_nonzero: assert property (
        @(posedge clk) disable iff ($initstate)
        (count != 4'b0000) |-> (done == 2'b00)
    );

    // done matches curr only when the counter has reached zero.
    check_done_matches_curr_when_count_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        (count == 4'b0000) |-> (done == curr)
    );

    // globalreset reloads the counter and clears curr on the next cycle.
    check_globalreset_loads_state: assert property (
        @(posedge clk) disable iff ($initstate)
        globalreset |=> (count == 4'b1000 && curr == 2'b00)
    );

    // reset reloads the counter and clears curr when globalreset is low.
    check_reset_loads_state: assert property (
        @(posedge clk) disable iff ($initstate)
        (!globalreset && reset) |=> (count == 4'b1000 && curr == 2'b00)
    );

    // A zero count causes the next cycle to reload the counter and clear curr.
    check_zero_count_reloads_state: assert property (
        @(posedge clk) disable iff ($initstate)
        (!globalreset && !reset && (count == 4'b0000))
        |=> (count == 4'b1000 && curr == 2'b00)
    );

    // A valid newresult decrements the counter.
    check_valid_newresult_decrements_count: assert property (
        @(posedge clk) disable iff ($initstate)
        (!globalreset && !reset && (count != 4'b0000) &&
         newresult && (resultID != 2'b00))
        |=> (count == ($past(count) - 4'b0001))
    );

    // A valid newresult updates curr with resultID.
    check_valid_newresult_updates_curr: assert property (
        @(posedge clk) disable iff ($initstate)
        (!globalreset && !reset && (count != 4'b0000) &&
         newresult && (resultID != 2'b00))
        |=> (curr == $past(resultID))
    );

    // Without reset, zero count, or a valid newresult, count holds.
    check_idle_holds_count: assert property (
        @(posedge clk) disable iff ($initstate)
        (!globalreset && !reset && (count != 4'b0000) &&
         !(newresult && (resultID != 2'b00)))
        |=> (count == $past(count))
    );

    // Without reset, zero count, or a valid newresult, curr holds.
    check_idle_holds_curr: assert property (
        @(posedge clk) disable iff ($initstate)
        (!globalreset && !reset && (count != 4'b0000) &&
         !(newresult && (resultID != 2'b00)))
        |=> (curr == $past(curr))
    );

    // The final valid decrement drives done with the accepted result ID.
    check_terminal_result_drives_done: assert property (
        @(posedge clk) disable iff ($initstate)
        (!globalreset && !reset && (count == 4'b0001) &&
         newresult && (resultID != 2'b00))
        |=> (count == 4'b0000 && curr == $past(resultID) && done == $past(resultID))
    );

endmodule