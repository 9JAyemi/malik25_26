module mux4_sva #(
    parameter int WIDTH = 8
) (
    input  logic [WIDTH-1:0] d0,
    input  logic [WIDTH-1:0] d1,
    input  logic [WIDTH-1:0] d2,
    input  logic [WIDTH-1:0] d3,
    input  logic [1:0]       s,
    input  logic [WIDTH-1:0] y
);
    ///// Mux behavior with 1-time-unit delay /////
    // y updates after 1 time unit (#1) to the selected input per s.
    check_y_mux_one_cycle_latency: assert property (
        @($global_clock) 1'b1 |=> (y == (s[1] ? (s[0] ? d3 : d2) : (s[0] ? d1 : d0)))
    );

    // When s==2'b00, y equals d0 on the next tick.
    check_sel_00: assert property (
        @($global_clock) (s == 2'b00) |=> (y == d0)
    );

    // When s==2'b01, y equals d1 on the next tick.
    check_sel_01: assert property (
        @($global_clock) (s == 2'b01) |=> (y == d1)
    );

    // When s==2'b10, y equals d2 on the next tick.
    check_sel_10: assert property (
        @($global_clock) (s == 2'b10) |=> (y == d2)
    );

    // When s==2'b11, y equals d3 on the next tick.
    check_sel_11: assert property (
        @($global_clock) (s == 2'b11) |=> (y == d3)
    );

    // If s and all data inputs are stable, y remains the same on the next tick.
    check_y_stable_when_inputs_stable: assert property (
        @($global_clock) $stable({s,d0,d1,d2,d3}) |=> (y == $past(y))
    );
endmodule