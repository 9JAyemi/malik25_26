module shift_reg_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic shift_left,
    input logic shift_right,
    input logic [15:0] data_in,
    input logic [15:0] data_out
);
    // Internal flag to ensure $past is valid one cycle after reset deasserts.
    logic past_valid;
    always @(posedge clk or posedge reset) begin
        if (reset) past_valid <= 1'b0;
        else       past_valid <= 1'b1;
    end

    // Load updates data_out with data_in on next cycle.
    check_load_updates_data_out: assert property (
        @(posedge clk) disable iff (reset) (past_valid && load) |=> (data_out == $past(data_in))
    );

    // Load has priority over any shift signals.
    check_load_priority_over_shifts: assert property (
        @(posedge clk) disable iff (reset) (past_valid && load && (shift_left || shift_right)) |=> (data_out == $past(data_in))
    );

    // Shift-left updates data_out with left-shifted previous value, LSB filled with 0.
    check_shift_left_updates: assert property (
        @(posedge clk) disable iff (reset) (past_valid && !load && shift_left) |=> (data_out == { $past(data_out[14:0]), 1'b0 })
    );

    // Shift-left inserts 0 into bit 0.
    check_shift_left_inserts_zero_lsb: assert property (
        @(posedge clk) disable iff (reset) (past_valid && !load && shift_left) |=> (data_out[0] == 1'b0)
    );

    // Shift-left moves bits [14:0] into [15:1].
    check_shift_left_moves_upper_bits: assert property (
        @(posedge clk) disable iff (reset) (past_valid && !load && shift_left) |=> (data_out[15:1] == $past(data_out[14:0]))
    );

    // Shift-right updates data_out with right-shifted previous value, MSB filled with 0.
    check_shift_right_updates: assert property (
        @(posedge clk) disable iff (reset) (past_valid && !load && !shift_left && shift_right) |=> (data_out == { 1'b0, $past(data_out[15:1]) })
    );

    // Shift-right inserts 0 into bit 15.
    check_shift_right_inserts_zero_msb: assert property (
        @(posedge clk) disable iff (reset) (past_valid && !load && !shift_left && shift_right) |=> (data_out[15] == 1'b0)
    );

    // Shift-right moves bits [15:1] into [14:0].
    check_shift_right_moves_lower_bits: assert property (
        @(posedge clk) disable iff (reset) (past_valid && !load && !shift_left && shift_right) |=> (data_out[14:0] == $past(data_out[15:1]))
    );

    // When both shifts are asserted (no load), left shift takes priority.
    check_shift_conflict_left_wins: assert property (
        @(posedge clk) disable iff (reset) (past_valid && !load && shift_left && shift_right) |=> (data_out == { $past(data_out[14:0]), 1'b0 })
    );

    // With no operation requested, data_out holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (reset) (past_valid && !load && !shift_left && !shift_right) |=> (data_out == $past(data_out))
    );
endmodule