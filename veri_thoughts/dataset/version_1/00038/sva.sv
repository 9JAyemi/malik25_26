module FSM_assertions #(
    parameter n = 4,
    parameter m = 2,
    parameter s = 8,
    parameter t = 12
) (
    input logic [n-1:0] in,
    input logic [m-1:0] out,
    input logic [s-1:0] state
);

    localparam logic [s-1:0] ST0 = {{(s-3){1'b0}}, 3'b000};
    localparam logic [s-1:0] ST1 = {{(s-3){1'b0}}, 3'b001};
    localparam logic [s-1:0] ST2 = {{(s-3){1'b0}}, 3'b010};
    localparam logic [s-1:0] ST3 = {{(s-3){1'b0}}, 3'b011};
    localparam logic [s-1:0] ST4 = {{(s-3){1'b0}}, 3'b100};
    localparam logic [s-1:0] ST5 = {{(s-3){1'b0}}, 3'b101};
    localparam logic [s-1:0] ST6 = {{(s-3){1'b0}}, 3'b110};
    localparam logic [s-1:0] ST7 = {{(s-3){1'b0}}, 3'b111};

    // State and output only change when the input vector changes.
    check_hold_when_input_stable: assert property (
        @($global_clock) disable iff ($initstate)
        $stable(in) |-> ($stable(state) && $stable(out))
    );

    // An invalid state encoding causes no assignment because there is no default case.
    check_invalid_state_holds_on_input_change: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed(in) &&
         ($past(state) != ST0) && ($past(state) != ST1) &&
         ($past(state) != ST2) && ($past(state) != ST3) &&
         ($past(state) != ST4) && ($past(state) != ST5) &&
         ($past(state) != ST6) && ($past(state) != ST7))
        |-> ($stable(state) && $stable(out))
    );

    // In states 0 or 1, in[0]&in[1] leads to state 1 with output 10.
    check_state01_cond_ab: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed(in) &&
         (($past(state) == ST0) || ($past(state) == ST1)) &&
         in[0] && in[1])
        |-> ((state == ST1) && (out == 2'b10))
    );

    // In states 2 or 3, in[0]&in[1] leads to state 3 with output 10.
    check_state23_cond_ab: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed(in) &&
         (($past(state) == ST2) || ($past(state) == ST3)) &&
         in[0] && in[1])
        |-> ((state == ST3) && (out == 2'b10))
    );

    // In states 0, 2, or 3, in[2] without in[0]&in[1] leads to state 2 with output 01.
    check_state023_cond_c: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed(in) &&
         (($past(state) == ST0) || ($past(state) == ST2) || ($past(state) == ST3)) &&
         !(in[0] && in[1]) && in[2])
        |-> ((state == ST2) && (out == 2'b01))
    );

    // In state 1, in[2] without in[0]&in[1] leads to state 3 with output 01.
    check_state1_cond_c: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed(in) &&
         ($past(state) == ST1) &&
         !(in[0] && in[1]) && in[2])
        |-> ((state == ST3) && (out == 2'b01))
    );

    // In states 0, 1, or 2, neither condition leads to state 0 with output 00.
    check_state012_else: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed(in) &&
         (($past(state) == ST0) || ($past(state) == ST1) || ($past(state) == ST2)) &&
         !(in[0] && in[1]) && !in[2])
        |-> ((state == ST0) && (out == 2'b00))
    );

    // In state 3, neither condition leads to state 1 with output 00.
    check_state3_else: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed(in) &&
         ($past(state) == ST3) &&
         !(in[0] && in[1]) && !in[2])
        |-> ((state == ST1) && (out == 2'b00))
    );

    // In states 4 or 5, in[1]&in[3] leads to state 5 with output 10.
    check_state45_cond_bd: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed(in) &&
         (($past(state) == ST4) || ($past(state) == ST5)) &&
         in[1] && in[3])
        |-> ((state == ST5) && (out == 2'b10))
    );

    // In states 6 or 7, in[1]&in[3] leads to state 7 with output 10.
    check_state67_cond_bd: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed(in) &&
         (($past(state) == ST6) || ($past(state) == ST7)) &&
         in[1] && in[3])
        |-> ((state == ST7) && (out == 2'b10))
    );

    // In states 4, 6, or 7, in[0] without in[1]&in[3] leads to state 6 with output 01.
    check_state467_cond_a: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed(in) &&
         (($past(state) == ST4) || ($past(state) == ST6) || ($past(state) == ST7)) &&
         !(in[1] && in[3]) && in[0])
        |-> ((state == ST6) && (out == 2'b01))
    );

    // In state 5, in[0] without in[1]&in[3] leads to state 7 with output 01.
    check_state5_cond_a: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed(in) &&
         ($past(state) == ST5) &&
         !(in[1] && in[3]) && in[0])
        |-> ((state == ST7) && (out == 2'b01))
    );

    // In states 4, 5, or 6, neither condition leads to state 4 with output 00.
    check_state456_else: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed(in) &&
         (($past(state) == ST4) || ($past(state) == ST5) || ($past(state) == ST6)) &&
         !(in[1] && in[3]) && !in[0])
        |-> ((state == ST4) && (out == 2'b00))
    );

    // In state 7, neither condition leads to state 5 with output 00.
    check_state7_else: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed(in) &&
         ($past(state) == ST7) &&
         !(in[1] && in[3]) && !in[0])
        |-> ((state == ST5) && (out == 2'b00))
    );

endmodule