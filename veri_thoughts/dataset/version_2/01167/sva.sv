module shift_register_sva (
    input logic CLK,
    input logic LOAD,
    input logic SHIFT,
    input logic [7:0] DATA_IN,
    input logic [7:0] Q_OUT,
    input logic [7:0] Q_BAR_OUT
);
    ///// Output complement relationship /////
    // Q_BAR_OUT is always bitwise inverse of Q_OUT.
    check_qbar_is_invert: assert property (
        @(posedge CLK) (Q_BAR_OUT == ~Q_OUT)
    );

    ///// LOAD behavior /////
    // On LOAD, next Q_OUT equals current DATA_IN (LOAD has priority over SHIFT).
    check_load_updates_qout: assert property (
        @(posedge CLK) LOAD |-> (Q_OUT == $past(DATA_IN))
    );

    ///// SHIFT behavior /////
    // On SHIFT without LOAD, next Q_OUT is left-shifted with DATA_IN[0] into bit 0.
    check_shift_updates_qout: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |-> (Q_OUT == { $past(Q_OUT[6:0]), $past(DATA_IN[0]) })
    );

    // On SHIFT without LOAD, next LSB comes from DATA_IN[0].
    check_shift_lsb_from_datain0: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |-> (Q_OUT[0] == $past(DATA_IN[0]))
    );

    // On SHIFT without LOAD, upper bits move down by one.
    check_shift_upper_bits_move_down: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |-> (Q_OUT[7:1] == $past(Q_OUT[6:0]))
    );

    ///// Hold behavior /////
    // With neither LOAD nor SHIFT, Q_OUT holds its value.
    check_hold_when_idle: assert property (
        @(posedge CLK) (!LOAD && !SHIFT) |-> (Q_OUT == $past(Q_OUT))
    );

    ///// Change causality /////
    // Any change in Q_OUT must be caused by a LOAD or SHIFT in the prior cycle.
    check_change_requires_load_or_shift: assert property (
        @(posedge CLK) ($past(1'b1) && $changed(Q_OUT)) |=> $past(LOAD || SHIFT)
    );
endmodule