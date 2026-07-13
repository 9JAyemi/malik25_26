module mux_4to1_sva(
    input logic       in0,
    input logic       in1,
    input logic       in2,
    input logic       in3,
    input logic [1:0] sel,
    input logic       out
);

    // Purely combinational mux with no RTL clock or reset; sample on the formal global clock.

    // out must match the exact RTL mux expression.
    check_mux_function: assert property (
        @($global_clock)
        out === ((sel == 2'b00) ? in0 :
                 (sel == 2'b01) ? in1 :
                 (sel == 2'b10) ? in2 :
                                  in3)
    );

    // sel=00 routes in0 to out.
    check_sel_00_routes_in0: assert property (
        @($global_clock)
        (sel === 2'b00) |-> (out === in0)
    );

    // sel=01 routes in1 to out.
    check_sel_01_routes_in1: assert property (
        @($global_clock)
        (sel === 2'b01) |-> (out === in1)
    );

    // sel=10 routes in2 to out.
    check_sel_10_routes_in2: assert property (
        @($global_clock)
        (sel === 2'b10) |-> (out === in2)
    );

    // sel=11 routes in3 to out.
    check_sel_11_routes_in3: assert property (
        @($global_clock)
        (sel === 2'b11) |-> (out === in3)
    );

endmodule