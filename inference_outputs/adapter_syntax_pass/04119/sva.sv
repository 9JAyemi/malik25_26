module shift_register_sva (
    input logic clk,
    input logic areset,
    input logic load,
    input logic ena,
    input logic [3:0] data,
    input logic [3:0] q
);

    // Active-low reset clears q to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) !areset |-> (q == 4'b0000)
    );

    // Load updates q with data on the next clock.
    check_load_updates_q: assert property (
        @(posedge clk) disable iff (!areset)
        load |=> (q == $past(data))
    );

    // Load has priority over enable when both are asserted.
    check_load_priority_over_enable: assert property (
        @(posedge clk) disable iff (!areset)
        (load && ena) |=> (q == $past(data))
    );

    // Enable rotates q left by one bit when load is low.
    check_enable_rotates_q: assert property (
        @(posedge clk) disable iff (!areset)
        (!load && ena) |=> (q == { $past(q[2:0]), $past(q[3]) })
    );

    // With no load or enable, q holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (!areset)
        (!load && !ena) |=> (q == $past(q))
    );

endmodule