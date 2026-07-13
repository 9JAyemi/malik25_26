module shift_register_sva (
    input logic       CLK,
    input logic       LOAD,
    input logic       SHIFT,
    input logic [3:0] DATA_IN,
    input logic [3:0] DATA_OUT
);

    // LOAD captures DATA_IN into the register on the next cycle.
    check_load_captures_data: assert property (
        @(posedge CLK)
        LOAD |=> (DATA_OUT == $past(DATA_IN))
    );

    // SHIFT rotates the stored value left when LOAD is low.
    check_shift_rotates_data: assert property (
        @(posedge CLK)
        (!LOAD && SHIFT) |=> (DATA_OUT == {$past(DATA_OUT[2:0]), $past(DATA_OUT[3])})
    );

    // The register holds its value when neither control is asserted.
    check_hold_without_control: assert property (
        @(posedge CLK)
        (!LOAD && !SHIFT) |=> (DATA_OUT == $past(DATA_OUT))
    );

    // LOAD takes priority over SHIFT when both are asserted.
    check_load_priority_over_shift: assert property (
        @(posedge CLK)
        (LOAD && SHIFT) |=> (DATA_OUT == $past(DATA_IN))
    );

endmodule