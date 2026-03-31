module shift_register_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic shift_right,
    input logic load,
    input logic [3:0] data_out
);

    // Load captures data_in into the register on the next cycle.
    check_load_captures_input: assert property (
        @(posedge clk) load |=> (data_out == $past(data_in))
    );

    // Load causes the register to hold its value on the next cycle.
    check_load_holds_value: assert property (
        @(posedge clk) load |=> (data_out == $past(data_out))
    );

    // Shift-right moves the previous stage4 value into stage1.
    check_shift_right_stage1: assert property (
        @(posedge clk) (!load && shift_right) |=> (data_out == $past(data_out))
    );

    // Shift-right moves the previous stage3 value into stage2.
    check_shift_right_stage2: assert property (
        @(posedge clk) (!load && shift_right) |=> ($past(data_out,2) == $past(data_out))
    );

    // Shift-right moves the previous stage2 value into stage3.
    check_shift_right_stage3: assert property (
        @(posedge clk) (!load && shift_right) |=> ($past(data_out,3) == $past(data_out))
    );

    // Shift-right moves the previous stage1 value into stage4.
    check_shift_right_stage4: assert property (
        @(posedge clk) (!load && shift_right) |=> ($past(data_out,4) == $past(data_out))
    );

    // No shift moves the previous stage3 value into stage1.
    check_no_shift_stage1: assert property (
        @(posedge clk) (!load && !shift_right) |=> (data_out == $past(data_out,3))
    );

    // No shift moves the previous stage2 value into stage2.
    check_no_shift_stage2: assert property (
        @(posedge clk) (!load && !shift_right) |=> ($past(data_out,2) == $past(data_out,4))
    );

    // No shift moves the previous stage1 value into stage3.
    check_no_shift_stage3: assert property (
        @(posedge clk) (!load && !shift_right) |=> ($past(data_out,3) == $past(data_out,5))
    );

    // No shift captures data_in into stage4.
    check_no_shift_stage4: assert property (
        @(posedge clk) (!load && !shift_right) |=> ($past(data_out,4) == $past(data_in))
    );

endmodule