module mux4to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic [3:0] out
);

    // When sel is 00, out must match in0.
    check_select_in0: assert property (
        @($global_clock) (sel === 2'b00) |-> (out === in0)
    );

    // When sel is 01, out must match in1.
    check_select_in1: assert property (
        @($global_clock) (sel === 2'b01) |-> (out === in1)
    );

    // When sel is 10, out must match in2.
    check_select_in2: assert property (
        @($global_clock) (sel === 2'b10) |-> (out === in2)
    );

    // When sel is 11, out must match in3.
    check_select_in3: assert property (
        @($global_clock) (sel === 2'b11) |-> (out === in3)
    );

    // If sel stays at 00 and in0 is stable, out must stay stable.
    check_hold_in0_when_selected: assert property (
        @($global_clock) ((sel === 2'b00) && $stable(sel) && $stable(in0)) |-> $stable(out)
    );

    // If sel stays at 01 and in1 is stable, out must stay stable.
    check_hold_in1_when_selected: assert property (
        @($global_clock) ((sel === 2'b01) && $stable(sel) && $stable(in1)) |-> $stable(out)
    );

    // If sel stays at 10 and in2 is stable, out must stay stable.
    check_hold_in2_when_selected: assert property (
        @($global_clock) ((sel === 2'b10) && $stable(sel) && $stable(in2)) |-> $stable(out)
    );

    // If sel stays at 11 and in3 is stable, out must stay stable.
    check_hold_in3_when_selected: assert property (
        @($global_clock) ((sel === 2'b11) && $stable(sel) && $stable(in3)) |-> $stable(out)
    );

endmodule