module mux_4to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] select,
    input logic [3:0] out
);

    // Combinational DUT sampled on the formal global clock.

    // When select is 00, out must match in0.
    check_select_00_routes_in0: assert property (
        @($global_clock) (select == 2'b00) |-> (out == in0)
    );

    // When select is 01, out must match in1.
    check_select_01_routes_in1: assert property (
        @($global_clock) (select == 2'b01) |-> (out == in1)
    );

    // When select is 10, out must match in2.
    check_select_10_routes_in2: assert property (
        @($global_clock) (select == 2'b10) |-> (out == in2)
    );

    // When select is 11, out must match in3.
    check_select_11_routes_in3: assert property (
        @($global_clock) (select == 2'b11) |-> (out == in3)
    );

endmodule