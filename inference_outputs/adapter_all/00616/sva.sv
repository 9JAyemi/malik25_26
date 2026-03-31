module FFType_sva (
    input logic clock,
    input logic reset,
    input logic io_in,
    input logic io_init,
    input logic io_out,
    input logic io_enable
);
    // Clock: clock (posedge). Reset: reset (synchronous, active-high). Sequential flop with enable.

    // io_out equals previous cycle's mux of reset/init vs enable/in.
    check_next_state_mux: assert property (
        @(posedge clock) disable iff (reset)
            io_out == $past(reset ? io_init : io_enable ? io_in : io_out)
    );

    // When reset is asserted, io_out loads io_init on the next cycle.
    check_reset_loads_init: assert property (
        @(posedge clock) reset |=> (io_out == $past(io_init))
    );

    // When reset is asserted, io_out is io_init on the same cycle.
    check_reset_sets_out_now: assert property (
        @(posedge clock) reset |-> (io_out == io_init)
    );

    // With enable and no reset, io_out loads io_in on the next cycle.
    check_enable_loads_in: assert property (
        @(posedge clock) disable iff (reset) io_enable |=> (io_out == $past(io_in))
    );

    // With enable low and no reset, io_out holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clock) disable iff (reset) !io_enable |=> (io_out == $past(io_out))
    );

    // If reset and enable are both asserted, reset has priority and io_out loads io_init.
    check_reset_priority_over_enable: assert property (
        @(posedge clock) (reset && io_enable) |=> (io_out == $past(io_init))
    );

    // If reset and enable are both asserted, io_out is io_init on the same cycle.
    check_reset_priority_sets_out_now: assert property (
        @(posedge clock) (reset && io_enable) |-> (io_out == io_init)
    );

    // If reset is held high across cycles, io_out equals the value loaded in the previous cycle.
    check_reset_hold_stability: assert property (
        @(posedge clock) (reset && $past(reset)) |-> (io_out == $past(io_out))
    );

    // If enable is held high across cycles and reset is low, io_out equals the value loaded in the previous cycle.
    check_enable_hold_stability: assert property (
        @(posedge clock) disable iff (reset) (io_enable && $past(io_enable)) |-> (io_out == $past(io_out))
    );

    // If reset is held high and enable is low, io_out loads io_init on the next cycle.
    check_reset_hold_loads_init: assert property (
        @(posedge clock) (reset && !io_enable && $past(reset && !io_enable)) |=> (io_out == $past(io_init))
    );

endmodule