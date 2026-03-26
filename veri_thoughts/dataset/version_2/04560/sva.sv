module shift_register_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic shift,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);

    // Reset clears the register on the following cycle.
    check_reset_clears_data: assert property (
        @(posedge clk) reset |=> (data_out == 4'b0000)
    );

    // Load captures data_in when shift is not asserted.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (reset)
        (load && !shift) |=> (data_out == $past(data_in))
    );

    // Shift rotates the register left when load is low.
    check_shift_rotates_data: assert property (
        @(posedge clk) disable iff (reset)
        (!load && shift) |=> (data_out == {$past(data_out[2]), $past(data_out[1]), $past(data_out[0]), $past(data_out[3])})
    );

    // The register holds its value when neither control is active.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !shift) |=> (data_out == $past(data_out))
    );

    // Load has priority over shift when both are asserted.
    check_load_priority_over_shift: assert property (
        @(posedge clk) disable iff (reset)
        (load && shift) |=> (data_out == $past(data_in))
    );

endmodule