module cont_test_sva #(parameter W = 4) (
    input logic clk,
    input logic rst,
    input logic load,
    input logic enable,
    input logic [W-1:0] d,
    input logic max_tick,
    input logic min_tick,
    input logic [W-1:0] q
);

    localparam logic [W-1:0] ZERO_VAL = {W{1'b0}};
    localparam logic [W-1:0] MAX_VAL  = {W{1'b1}};
    localparam logic [W-1:0] ONE_VAL  = {{(W-1){1'b0}}, 1'b1};

    // A sampled reset leaves the counter in the zero state by the next cycle.
    check_reset_clears_state: assert property (
        @(posedge clk) rst |=> (q == ZERO_VAL) && min_tick && !max_tick
    );

    // max_tick is asserted exactly when q is all ones.
    check_max_tick_decode: assert property (
        @(posedge clk) disable iff (rst) max_tick == (q == MAX_VAL)
    );

    // min_tick is asserted exactly when q is zero.
    check_min_tick_decode: assert property (
        @(posedge clk) disable iff (rst) min_tick == (q == ZERO_VAL)
    );

    // max_tick and min_tick cannot be high at the same time.
    check_ticks_mutually_exclusive: assert property (
        @(posedge clk) disable iff (rst) !(max_tick && min_tick)
    );

    // When enabled with load high, q takes d on the next cycle.
    check_load_updates_q: assert property (
        @(posedge clk) disable iff (rst) (enable && load) |=> (q == $past(d))
    );

    // A load also drives the tick outputs from the loaded value.
    check_load_updates_ticks: assert property (
        @(posedge clk) disable iff (rst)
        (enable && load) |=> ((max_tick == ($past(d) == MAX_VAL)) &&
                              (min_tick == ($past(d) == ZERO_VAL)))
    );

    // When enabled without load, q increments by one modulo 2^W.
    check_increment_updates_q: assert property (
        @(posedge clk) disable iff (rst) (enable && !load) |=> (q == ($past(q) + ONE_VAL))
    );

    // When not enabled, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst) (!enable) |=> (q == $past(q))
    );

    // Incrementing from the maximum value wraps q to zero.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (rst)
        (enable && !load && (q == MAX_VAL)) |=> (q == ZERO_VAL) && min_tick && !max_tick
    );

endmodule