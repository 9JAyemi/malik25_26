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

// Shift-right moves the previous data_out value into the register.
    check_shift_right_moves_data: assert property (
        @(posedge clk) (!load && shift_right) |=> (data_out == $past(data_out))
    );

// Shift-left moves the previous data_in value into the register.
    check_shift_left_moves_data: assert property (
        @(posedge clk) (!load && !shift_right) |=> (data_out == $past(data_in))
    );

// With no control asserted, the register holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) (!load && !shift_right) |=> (data_out == $past(data_out))
    );

// Four consecutive loads return the input value four cycles later.
    check_four_loads_return_input: assert property (
        @(posedge clk) (load[*4]) |=> (data_out == $past(data_in, 4))
    );

// Four consecutive shift-right operations return the value four cycles later.
    check_four_shift_right_return_value: assert property (
        @(posedge clk) (!load && shift_right[*4]) |=> (data_out == $past(data_out, 4))
    );

// Four consecutive shift-left operations return the value four cycles later.
    check_four_shift_left_return_value: assert property (
        @(posedge clk) (!load && !shift_right[*4]) |=> (data_out == $past(data_in, 4))
    );

endmodule
