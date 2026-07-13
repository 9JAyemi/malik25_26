module shift_register_sva(
    input logic clk,
    input logic load,
    input logic [3:0] data_in,
    input logic shift,
    input logic [3:0] data_out
);

    // Load captures data_in into data_out on the next clock.
    check_load_captures_input: assert property (
        @(posedge clk) load |=> (data_out == $past(data_in))
    );

    // Load takes priority over shift when both are asserted.
    check_load_has_priority_over_shift: assert property (
        @(posedge clk) (load && shift) |=> (data_out == $past(data_in))
    );

    // Shift moves bits left and inserts 0 into bit 0 when load is low.
    check_shift_left_zero_fill: assert property (
        @(posedge clk) (!load && shift) |=> ((data_out[3:1] == $past(data_out[2:0])) && (data_out[0] == 1'b0))
    );

    // With neither load nor shift asserted, the register holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) (!load && !shift) |=> (data_out == $past(data_out))
    );

    // Any output change must come from a load or shift in the prior cycle.
    check_output_change_requires_command: assert property (
        @(posedge clk) !$initstate && (data_out != $past(data_out)) |-> ($past(load) || $past(shift))
    );

endmodule