module register_4bit_sva (
    input logic [3:0] data_in,
    input logic       load,
    input logic       reset,
    input logic       clk,
    input logic [3:0] Q
);

// Reset drives Q to zero on the next sampled cycle.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |=> (Q == 4'b0000)
    );

// With load high, Q captures data_in on the next sampled cycle.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (reset) load |=> (Q == $past(data_in))
    );

// With load low, Q holds its previous value on the next sampled cycle.
    check_hold_when_load_low: assert property (
        @(posedge clk) disable iff (reset) !load |=> (Q == $past(Q))
    );

endmodule
