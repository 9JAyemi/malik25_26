module shift_adder_sva (
    input logic CLK,
    input logic LOAD,
    input logic SHIFT,
    input logic [7:0] DATA_IN,
    input logic [7:0] Q_OUT,
    input logic [7:0] Q_BAR_OUT
);
    // Clock: CLK (posedge). No reset present.
    // Logic: Mixed (sequential shift_reg; combinational complement and adder).
    // Behavior: LOAD captures DATA_IN; else if SHIFT shifts right with MSB from DATA_IN[7]; else hold. Q_BAR_OUT is ~Q_OUT.

    // Q_BAR_OUT is always the bitwise complement of Q_OUT.
    check_complement_always: assert property (
        @(posedge CLK) (Q_BAR_OUT == ~Q_OUT)
    );

    // LOAD updates Q_OUT with DATA_IN on the next cycle (SHIFT ignored if also high).
    check_load_updates_qout: assert property (
        @(posedge CLK) LOAD |-> ##1 (Q_OUT == $past(DATA_IN))
    );

    // When SHIFT and not LOAD, next Q_OUT equals {DATA_IN[7], previous Q_OUT[7:1]}.
    check_shift_right_vector: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |-> ##1 (Q_OUT == { $past(DATA_IN[7]), $past(Q_OUT[7:1]) })
    );

    // SHIFT (without LOAD) updates MSB with DATA_IN[7] on the next cycle.
    check_shift_msb_update: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |-> ##1 (Q_OUT[7] == $past(DATA_IN[7]))
    );

    // SHIFT (without LOAD) shifts lower bits right by one on the next cycle.
    check_shift_lower_bits_update: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |-> ##1 (Q_OUT[6:0] == $past(Q_OUT[7:1]))
    );

    // When neither LOAD nor SHIFT, Q_OUT holds its value to the next cycle.
    check_hold_when_idle: assert property (
        @(posedge CLK) (!LOAD && !SHIFT) |-> ##1 (Q_OUT == $past(Q_OUT))
    );

    // After LOAD, Q_BAR_OUT reflects the complement of the loaded DATA_IN.
    check_load_updates_qbar: assert property (
        @(posedge CLK) LOAD |-> ##1 (Q_BAR_OUT == ~($past(DATA_IN)))
    );

    // After SHIFT (without LOAD), Q_BAR_OUT reflects complement of the shifted result.
    check_shift_updates_qbar: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |-> ##1 (Q_BAR_OUT == ~{ $past(DATA_IN[7]), $past(Q_OUT[7:1]) })
    );

    // Any change in Q_OUT by next cycle requires LOAD or SHIFT in the previous cycle.
    check_change_requires_enable: assert property (
        @(posedge CLK) 1'b1 |-> ##1 ( (Q_OUT == $past(Q_OUT)) || ($past(LOAD) || $past(SHIFT)) )
    );

    // LOAD has priority over SHIFT when both are asserted.
    check_load_priority_over_shift: assert property (
        @(posedge CLK) (LOAD && SHIFT) |-> ##1 (Q_OUT == $past(DATA_IN))
    );
endmodule