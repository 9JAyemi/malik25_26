module register_4bit_sva (
    input logic [3:0] data_in,
    input logic       load,
    input logic       reset,
    input logic       clk,
    input logic [3:0] Q
);

    // Reset forces the register output to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |-> (Q == 4'b0000)
    );

    // Reset has priority over load when both are asserted.
    check_reset_priority_over_load: assert property (
        @(posedge clk) (reset && load) |-> (Q == 4'b0000)
    );

    // With load asserted, the next sampled output matches the input.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (reset) load |=> (Q == $past(data_in))
    );

    // With load deasserted, the output holds its previous value.
    check_hold_when_load_deasserted: assert property (
        @(posedge clk) disable iff (reset) !load |=> (Q == $past(Q))
    );

endmodule