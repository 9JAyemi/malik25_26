module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count,
    input logic mux_out
);

// Clock: clk (posedge). Reset: rst (active-high, synchronous). Logic: mixed (sequential counter with combinational mux).

    // On reset, count is 0 on the next cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'h0)
    );

// On reset, mux_out is 0 on the next cycle.
    check_reset_clears_mux_out: assert property (
        @(posedge clk) rst |=> (mux_out == 1'b0)
    );

// When not at max, count increments by 1 each cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst) (count != 4'hF) |=> (count == ($past(count) + 4'h1))
    );

// When at max, count wraps to 0 on the next cycle.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (rst) (count == 4'hF) |=> (count == 4'h0)
    );

// Mux selects count[0] when S is 1.
    check_mux_selects_bit0_when_s1: assert property (
        @(posedge clk) disable iff (rst) (count[0] == 1'b1) |-> (mux_out == 1'b1)
    );

// Mux selects 0 when S is 0.
    check_mux_selects_zero_when_s0: assert property (
        @(posedge clk) disable iff (rst) (count[0] == 1'b0) |-> (mux_out == 1'b0)
    );

endmodule
