module shift_register_sva (
    input logic       clk,
    input logic       reset,
    input logic [7:0] data_in,
    input logic [1:0] shift_direction,
    input logic       load,
    input logic [7:0] data_out
);

    // A reset edge clears the output by the next sampled event.
    check_reset_clears_by_next_event: assert property (
        @(negedge clk or posedge reset)
        $rose(reset) |=> (data_out == 8'h00)
    );

    // Once reset is active across sampled events, the output stays zero.
    check_reset_holds_zero_while_active: assert property (
        @(negedge clk or posedge reset) disable iff ($initstate)
        (reset && $past(reset)) |-> (data_out == 8'h00)
    );

    // Load captures data_in on the active clock edge.
    check_load_captures_data_in: assert property (
        @(negedge clk or posedge reset) disable iff (reset)
        load |=> (data_out == $past(data_in))
    );

    // With no load, direction 00 rotates the register right by one bit.
    check_shift_right_rotate: assert property (
        @(negedge clk or posedge reset) disable iff (reset)
        (!load && (shift_direction == 2'b00)) |=> (data_out == $past({data_out[0], data_out[7:1]}))
    );

    // With no load, direction 01 rotates the register left by one bit.
    check_shift_left_rotate: assert property (
        @(negedge clk or posedge reset) disable iff (reset)
        (!load && (shift_direction == 2'b01)) |=> (data_out == $past({data_out[6:0], data_out[7]}))
    );

    // With no load, directions 10 and 11 hold the current value.
    check_invalid_direction_holds_value: assert property (
        @(negedge clk or posedge reset) disable iff (reset)
        (!load && ((shift_direction == 2'b10) || (shift_direction == 2'b11))) |=> (data_out == $past(data_out))
    );

endmodule