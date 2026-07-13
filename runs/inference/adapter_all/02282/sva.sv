module shift_register_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic shift_right,
    input logic load,
    input logic [3:0] data_out
);

    // Load captures data_in into the register on the next cycle.
    check_load_captures_data: assert property (
        @(posedge clk) load |=> (data_out == $past(data_in))
    );

    // Load has priority over shift_right when both are asserted.
    check_load_priority_over_shift: assert property (
        @(posedge clk) (load && shift_right) |=> (data_out == $past(data_in))
    );

    // With shift_right asserted and load deasserted, the register shifts right.
    check_shift_right_behavior: assert property (
        @(posedge clk) (!load && shift_right) |=> (data_out == $past(data_out))
    );

    // With shift_right deasserted and load deasserted, the register shifts left.
    check_shift_left_behavior: assert property (
        @(posedge clk) (!load && !shift_right) |=> (data_out == $past(data_out, 4))
    );

    // Four consecutive shift-right cycles return the register to its original value.
    check_four_shift_right_cycles_return: assert property (
        @(posedge clk) (!load && shift_right)[*4] |=> (data_out == $past(data_out, 4))
    );

    // Four consecutive shift-left cycles return the register to its original value.
    check_four_shift_left_cycles_return: assert property (
        @(posedge clk) (!load && !shift_right)[*4] |=> (data_out == $past(data_out, 4))
    );

endmodule