module shift_register_sva (
    input logic       clk,
    input logic       load,
    input logic       shift,
    input logic [3:0] in,
    input logic [3:0] out
);

    // Load copies the input when shift is low.
    check_load_only_captures_input: assert property (
        @(posedge clk) (load && !shift) |=> out == $past(in)
    );

    // Load has priority over shift when both controls are high.
    check_load_priority_over_shift: assert property (
        @(posedge clk) (load && shift) |=> out == $past(in)
    );

    // Shift inserts a zero into bit 0.
    check_shift_clears_lsb: assert property (
        @(posedge clk) (!load && shift) |=> out[0] == 1'b0
    );

    // Shift moves the previous bit 0 into bit 1.
    check_shift_moves_bit1: assert property (
        @(posedge clk) (!load && shift) |=> out[1] == $past(out[0])
    );

    // Shift moves the previous bit 1 into bit 2.
    check_shift_moves_bit2: assert property (
        @(posedge clk) (!load && shift) |=> out[2] == $past(out[1])
    );

    // Shift moves the previous bit 2 into bit 3.
    check_shift_moves_bit3: assert property (
        @(posedge clk) (!load && shift) |=> out[3] == $past(out[2])
    );

    // Without load or shift, the register holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) (!load && !shift) |=> out == $past(out)
    );

endmodule