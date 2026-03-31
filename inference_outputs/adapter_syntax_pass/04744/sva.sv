module mux_4to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] select,
    input logic [3:0] out
);

    // select=00 routes in0 to out.
    check_select_00_routes_in0: assert property (
        @($global_clock) (select == 2'b00) |-> (out == in0)
    );

    // select=01 routes in1 to out.
    check_select_01_routes_in1: assert property (
        @($global_clock) (select == 2'b01) |-> (out == in1)
    );

    // select=10 routes in2 to out.
    check_select_10_routes_in2: assert property (
        @($global_clock) (select == 2'b10) |-> (out == in2)
    );

    // select=11 routes in3 to out.
    check_select_11_routes_in3: assert property (
        @($global_clock) (select == 2'b11) |-> (out == in3)
    );

endmodule