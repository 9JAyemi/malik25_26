module priority_mux_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic       PRI,
    input logic [1:0] SEL,
    input logic [3:0] out
);

    // No RTL clock or reset; sample this combinational DUT on the formal global clock.

    // Priority mode selects in3 when it is nonzero.
    check_pri_selects_in3: assert property (
        @($global_clock) disable iff (1'b0)
        (PRI && (in3 != 4'b0000)) |-> (out == in3)
    );

    // Priority mode selects in2 when in3 is zero and in2 is nonzero.
    check_pri_selects_in2: assert property (
        @($global_clock) disable iff (1'b0)
        (PRI && (in3 == 4'b0000) && (in2 != 4'b0000)) |-> (out == in2)
    );

    // Priority mode selects in1 when in3 and in2 are zero and in1 is nonzero.
    check_pri_selects_in1: assert property (
        @($global_clock) disable iff (1'b0)
        (PRI && (in3 == 4'b0000) && (in2 == 4'b0000) && (in1 != 4'b0000)) |-> (out == in1)
    );

    // Priority mode falls back to in0 when higher-priority inputs are zero.
    check_pri_falls_back_to_in0: assert property (
        @($global_clock) disable iff (1'b0)
        (PRI && (in3 == 4'b0000) && (in2 == 4'b0000) && (in1 == 4'b0000)) |-> (out == in0)
    );

    // Select mode with SEL=00 routes in0.
    check_sel_00_selects_in0: assert property (
        @($global_clock) disable iff (1'b0)
        ((!PRI) && (SEL == 2'b00)) |-> (out == in0)
    );

    // Select mode with SEL=01 routes in1.
    check_sel_01_selects_in1: assert property (
        @($global_clock) disable iff (1'b0)
        ((!PRI) && (SEL == 2'b01)) |-> (out == in1)
    );

    // Select mode with SEL=10 routes in2.
    check_sel_10_selects_in2: assert property (
        @($global_clock) disable iff (1'b0)
        ((!PRI) && (SEL == 2'b10)) |-> (out == in2)
    );

    // Select mode with SEL=11 routes in3.
    check_sel_11_selects_in3: assert property (
        @($global_clock) disable iff (1'b0)
        ((!PRI) && (SEL == 2'b11)) |-> (out == in3)
    );

    // Priority mode always matches one of the implemented priority branches.
    check_pri_mode_behavior: assert property (
        @($global_clock) disable iff (1'b0)
        PRI |-> (
            ((in3 != 4'b0000) && (out == in3)) ||
            ((in3 == 4'b0000) && (in2 != 4'b0000) && (out == in2)) ||
            ((in3 == 4'b0000) && (in2 == 4'b0000) && (in1 != 4'b0000) && (out == in1)) ||
            ((in3 == 4'b0000) && (in2 == 4'b0000) && (in1 == 4'b0000) && (out == in0))
        )
    );

    // Select mode always matches the implemented SEL decode.
    check_sel_mode_behavior: assert property (
        @($global_clock) disable iff (1'b0)
        (!PRI) |-> (
            ((SEL == 2'b00) && (out == in0)) ||
            ((SEL == 2'b01) && (out == in1)) ||
            ((SEL == 2'b10) && (out == in2)) ||
            ((SEL == 2'b11) && (out == in3))
        )
    );

endmodule