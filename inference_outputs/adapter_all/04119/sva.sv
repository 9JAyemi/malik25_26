module shift_register_sva (
    input logic clk,
    input logic areset,
    input logic load,
    input logic ena,
    input logic [3:0] data,
    input logic [3:0] q
);

    // Active-low reset forces q low.
    check_reset_clears_q: assert property (
        @(posedge clk) !areset |-> (q == 4'b0000)
    );

    // Reset has priority over load.
    check_reset_priority_over_load: assert property (
        @(posedge clk) (!areset && load) |-> (q == 4'b0000)
    );

    // Reset has priority over enable.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (!areset && ena) |-> (q == 4'b0000)
    );

    // Load captures data into q.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (!areset) load |=> (q == $past(data))
    );

    // Enable rotates q left when load is low.
    check_enable_rotates_q: assert property (
        @(posedge clk) disable iff (!areset) (!load && ena) |=> (q == {$past(q[2:0]), $past(q[3])})
    );

    // With no load or enable, q holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (!areset) (!load && !ena) |=> (q == $past(q))
    );

endmodule