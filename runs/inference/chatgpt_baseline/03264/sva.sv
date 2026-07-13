module up_down_counter_sva (
    input logic up_down,
    input logic clear,
    input logic load,
    input logic [3:0] data_in,
    input logic clk,
    input logic [3:0] count_out
);

    // If clear stays low across clocks, the counter must be zero.
    check_clear_holds_zero: assert property (
        @(posedge clk)
        (!clear ##1 !clear) |-> (count_out == 4'b0000)
    );

    // Load captures data_in on the next clock unless async clear forces zero.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (!clear)
        load |=> ((count_out == $past(data_in)) || (count_out == 4'b0000))
    );

    // Without load, up_down high increments on the next clock unless async clear forces zero.
    check_increment_behavior: assert property (
        @(posedge clk) disable iff (!clear)
        (!load && up_down) |=> ((count_out == ($past(count_out) + 4'b0001)) || (count_out == 4'b0000))
    );

    // Without load, up_down low decrements on the next clock unless async clear forces zero.
    check_decrement_behavior: assert property (
        @(posedge clk) disable iff (!clear)
        (!load && !up_down) |=> ((count_out == ($past(count_out) - 4'b0001)) || (count_out == 4'b0000))
    );

endmodule