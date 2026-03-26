module mux4to1_sva (
    input logic [1:0] sel,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [3:0] out
);

    // out matches the RTL mux expression.
    check_mux_function: assert property (
        @($global_clock)
        out === ((sel == 2'b00) ? in0 :
                 (sel == 2'b01) ? in1 :
                 (sel == 2'b10) ? in2 :
                                  in3)
    );

    // sel=00 routes in0 to out.
    check_sel00_routes_in0: assert property (
        @($global_clock)
        (sel === 2'b00) |-> (out === in0)
    );

    // sel=01 routes in1 to out.
    check_sel01_routes_in1: assert property (
        @($global_clock)
        (sel === 2'b01) |-> (out === in1)
    );

    // sel=10 routes in2 to out.
    check_sel10_routes_in2: assert property (
        @($global_clock)
        (sel === 2'b10) |-> (out === in2)
    );

    // sel=11 routes in3 to out.
    check_sel11_routes_in3: assert property (
        @($global_clock)
        (sel === 2'b11) |-> (out === in3)
    );

endmodule