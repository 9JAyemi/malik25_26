module top_module_sva (
    input logic clk,
    input logic areset,
    input logic load,
    input logic ena,
    input logic [3:0] data,
    input logic [3:0] q
);

    // Reset forces q to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) areset |-> (q == 4'b0000)
    );

    // Load updates q with data on the next cycle.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (areset)
        load |=> (q == $past(data))
    );

    // With load low, q shifts right by one bit.
    check_shift_updates_q: assert property (
        @(posedge clk) disable iff (areset)
        (!load && ena) |=> (q == {1'b0, $past(q[3:1])})
    );

    // With both load and enable high, q captures data.
    check_load_has_priority_over_shift: assert property (
        @(posedge clk) disable iff (areset)
        (load && ena) |=> (q == $past(data))
    );

    // With load low and enable low, q holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (areset)
        (!load && !ena) |=> (q == $past(q))
    );

endmodule