module shift_register_sva (
    input logic       CLK,
    input logic       EN,
    input logic       TE,
    input logic       DATA_IN,
    input logic [3:0] DATA_OUT
);

    // Sequential logic is clocked by CLK; no reset is present in the RTL.
    // TE is an input port but is not used by this implementation.

    // When enabled, bits [3:1] take the previous values of bits [2:0].
    check_shift_upper_bits_when_enabled: assert property (
        @(posedge CLK) disable iff ($initstate)
        EN |=> (DATA_OUT[3:1] == $past(DATA_OUT[2:0]))
    );

    // When enabled, bit 0 captures the previous DATA_IN value.
    check_shift_lsb_when_enabled: assert property (
        @(posedge CLK) disable iff ($initstate)
        EN |=> (DATA_OUT[0] == $past(DATA_IN))
    );

    // When not enabled, DATA_OUT holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge CLK) disable iff ($initstate)
        !EN |=> (DATA_OUT == $past(DATA_OUT))
    );

endmodule