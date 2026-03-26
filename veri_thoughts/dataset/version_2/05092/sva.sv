module priority_encoder_sva (
    input logic [1:0] data,
    input logic       clk,
    input logic       q
);

    // q captures data[1] from the previous clock.
    check_q_captures_data1: assert property (
        @(posedge clk) disable iff ($initstate) q == $past(data[1])
    );

    // A high data[1] is reflected in q on the next clock.
    check_data1_high_sets_q: assert property (
        @(posedge clk) disable iff ($initstate) data[1] |=> q
    );

    // A low data[1] is reflected in q on the next clock.
    check_data1_low_clears_q: assert property (
        @(posedge clk) disable iff ($initstate) !data[1] |=> !q
    );

    // Stable data[1] produces stable q on the following cycle.
    check_stable_data1_keeps_q_stable: assert property (
        @(posedge clk) disable iff ($initstate) $stable(data[1]) |=> $stable(q)
    );

    // A change on data[1] causes q to change on the following cycle.
    check_changed_data1_changes_q: assert property (
        @(posedge clk) disable iff ($initstate) $changed(data[1]) |=> $changed(q)
    );

    // data[0] changes alone do not affect q.
    check_data0_ignored_when_data1_stable: assert property (
        @(posedge clk) disable iff ($initstate) ($changed(data[0]) && $stable(data[1])) |=> $stable(q)
    );

endmodule