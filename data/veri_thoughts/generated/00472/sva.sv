module shift_register_sva (
    input logic [3:0] DATA_IN,
    input logic       SHIFT_EN,
    input logic       LOAD_EN,
    input logic       CLK,
    input logic [3:0] DATA_OUT
);

    // LOAD_EN captures DATA_IN on the next cycle.
    check_load_captures_input: assert property (
        @(posedge CLK) LOAD_EN |=> (DATA_OUT == $past(DATA_IN))
    );

    // LOAD_EN has priority over SHIFT_EN when both are high.
    check_load_priority_over_shift: assert property (
        @(posedge CLK) (LOAD_EN && SHIFT_EN) |=> (DATA_OUT == $past(DATA_IN))
    );

    // SHIFT_EN rotates the register left with wraparound when LOAD_EN is low.
    check_shift_rotate_left: assert property (
        @(posedge CLK) (!LOAD_EN && SHIFT_EN) |=> (
            (DATA_OUT[3] == $past(DATA_OUT[2])) &&
            (DATA_OUT[2] == $past(DATA_OUT[1])) &&
            (DATA_OUT[1] == $past(DATA_OUT[0])) &&
            (DATA_OUT[0] == $past(DATA_OUT[3]))
        )
    );

    // With both enables low, DATA_OUT holds its value.
    check_hold_when_idle: assert property (
        @(posedge CLK) (!LOAD_EN && !SHIFT_EN) |=> (DATA_OUT == $past(DATA_OUT))
    );

endmodule