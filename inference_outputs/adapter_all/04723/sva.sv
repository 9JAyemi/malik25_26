module shift_register_sva (
    input logic clk,
    input logic areset,
    input logic load,
    input logic ena,
    input logic [3:0] data,
    input logic [3:0] q
);

    // Reset forces q low.
    check_reset_clears_q: assert property (
        @(posedge clk) areset |-> (q == 4'b0000)
    );

    // Reset has priority over load.
    check_reset_priority_over_load: assert property (
        @(posedge clk) (areset && load) |-> (q == 4'b0000)
    );

    // Reset has priority over enable.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (areset && ena) |-> (q == 4'b0000)
    );

    // Reset has priority over both load and enable.
    check_reset_priority_over_both: assert property (
        @(posedge clk) (areset && load && ena) |-> (q == 4'b0000)
    );

    // Load captures data when enable is low.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (areset) (!ena && load) |-> (q == data)
    );

    // Enable shifts q left when load is low.
    check_enable_shifts_q: assert property (
        @(posedge clk) disable iff (areset) (!load && ena) |-> (q == {1'b0, $past(q[3:1])})
    );

    // With both load and enable low, q holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (areset) (!load && !ena) |-> (q == $past(q))
    );

    // With both load and enable high, load has priority.
    check_load_priority_over_enable: assert property (
        @(posedge clk) disable iff (areset) (load && ena) |-> (q == data)
    );

    // With both load and enable high, q still shifts left.
    check_shift_after_load: assert property (
        @(posedge clk) disable iff (areset) (load && ena) |-> (q == {1'b0, $past(q[3:1])})
    );

endmodule