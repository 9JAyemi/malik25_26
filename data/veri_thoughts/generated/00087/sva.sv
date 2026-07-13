module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic [3:0] load_value,
    input logic [3:0] q,
    input logic carry_out,
    input logic led
);

    // If reset is sampled low, the next sampled state is 5 and the status outputs are low.
    check_reset_state: assert property (
        @(posedge clk) (!reset) |=> ((q == 4'h5) && (carry_out == 1'b0) && (led == 1'b0))
    );

    // With load high, q takes load_value on the next cycle unless async reset intervenes.
    check_load_updates_q: assert property (
        @(posedge clk) disable iff (!reset)
        load |=> ((q == $past(load_value)) || (q == 4'h5))
    );

    // Without load, q increments by one when it is not at 15 unless async reset intervenes.
    check_increment_nonterminal: assert property (
        @(posedge clk) disable iff (!reset)
        (!load && (q != 4'hF)) |=> ((q == ($past(q) + 4'd1)) || (q == 4'h5))
    );

    // Without load, q wraps from 15 to 0 unless async reset intervenes.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (!reset)
        (!load && (q == 4'hF)) |=> ((q == 4'h0) || (q == 4'h5))
    );

    // carry_out is high exactly when q is 15.
    check_carry_matches_q: assert property (
        @(posedge clk) disable iff (!reset)
        (carry_out == (q == 4'hF))
    );

    // led always mirrors carry_out.
    check_led_matches_carry: assert property (
        @(posedge clk) disable iff (!reset)
        (led == carry_out)
    );

endmodule