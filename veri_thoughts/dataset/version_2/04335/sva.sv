module shift_register_sva (
    input logic [3:0] DATA_IN,
    input logic       SHIFT_EN,
    input logic       LOAD_EN,
    input logic       CLK,
    input logic [3:0] DATA_OUT
);

    // A load updates the register with DATA_IN.
    check_load_captures_input: assert property (
        @(posedge CLK) LOAD_EN |=> (DATA_OUT == $past(DATA_IN))
    );

    // Load takes priority when both load and shift are asserted.
    check_load_priority_over_shift: assert property (
        @(posedge CLK) (LOAD_EN && SHIFT_EN) |=> (DATA_OUT == $past(DATA_IN))
    );

    // A shift rotates the previous MSB into bit 0.
    check_shift_rotates_left: assert property (
        @(posedge CLK) (!LOAD_EN && SHIFT_EN) |=> (DATA_OUT == { $past(DATA_OUT[2:0]), $past(DATA_OUT[3]) })
    );

    // With both enables low, the register holds its value.
    check_hold_when_disabled: assert property (
        @(posedge CLK) (!LOAD_EN && !SHIFT_EN) |=> (DATA_OUT == $past(DATA_OUT))
    );

endmodule