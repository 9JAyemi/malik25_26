module shift_register_4bit_sva(
    input logic clk,
    input logic rst,
    input logic load,
    input logic [3:0] data_in,
    input logic shift,
    input logic [3:0] data_out
);

    // Reset forces the register output low.
    check_reset_clears_data_out: assert property (
        @(posedge clk) !rst |-> (data_out == 4'b0000)
    );

    // Load alone captures data_in on the next clock.
    check_load_captures_data_in: assert property (
        @(posedge clk) disable iff (!rst)
        (load && !shift) |=> (data_out == $past(data_in))
    );

    // Load has priority when load and shift are both asserted.
    check_load_priority_over_shift: assert property (
        @(posedge clk) disable iff (!rst)
        (load && shift) |=> (data_out == $past(data_in))
    );

    // Shift alone moves the register left and inserts zero.
    check_shift_left_with_zero_fill: assert property (
        @(posedge clk) disable iff (!rst)
        (!load && shift) |=> (data_out == {$past(data_out[2:0]), 1'b0})
    );

    // With no load or shift, the register holds its value.
    check_idle_holds_value: assert property (
        @(posedge clk) disable iff (!rst)
        (!load && !shift) |=> (data_out == $past(data_out))
    );

endmodule