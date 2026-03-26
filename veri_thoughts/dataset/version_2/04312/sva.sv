module mux_4to1_sva (
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic sel1,
    input logic sel2,
    input logic out
);

    // Output matches the RTL mux equation.
    check_mux_equation: assert property (
        @($global_clock)
        out == ((sel1 & sel2) ? in3 :
                ((sel1 & ~sel2) ? in2 :
                 ((~sel1 & sel2) ? in1 : in0)))
    );

    // sel1=0 and sel2=0 selects in0.
    check_select_in0: assert property (
        @($global_clock)
        (!sel1 && !sel2) |-> (out == in0)
    );

    // sel1=0 and sel2=1 selects in1.
    check_select_in1: assert property (
        @($global_clock)
        (!sel1 && sel2) |-> (out == in1)
    );

    // sel1=1 and sel2=0 selects in2.
    check_select_in2: assert property (
        @($global_clock)
        (sel1 && !sel2) |-> (out == in2)
    );

    // sel1=1 and sel2=1 selects in3.
    check_select_in3: assert property (
        @($global_clock)
        (sel1 && sel2) |-> (out == in3)
    );

endmodule