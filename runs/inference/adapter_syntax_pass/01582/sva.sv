module register_4bit_sva (
    input logic [3:0] data_in,
    input logic       load,
    input logic       reset,
    input logic       clk,
    input logic [3:0] Q
);

    // Reset forces the registered output to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |-> (Q == 4'b0000)
    );

    // A load cycle captures data_in into Q on the next clock.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (Q == $past(data_in))
    );

    // Without load, Q holds its previous value.
    check_hold_when_not_loading: assert property (
        @(posedge clk) disable iff (reset)
        !load |=> (Q == $past(Q))
    );

endmodule