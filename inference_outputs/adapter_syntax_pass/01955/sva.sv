module mux4to1_32_sva (
    input logic [1:0] sel,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] c,
    input logic [31:0] d,
    input logic [31:0] o
);

    // sel=00 routes a to o.
    check_sel_00_routes_a: assert property (
        @($global_clock) (sel == 2'b00) |-> (o == a)
    );

    // sel=01 routes b to o.
    check_sel_01_routes_b: assert property (
        @($global_clock) (sel == 2'b01) |-> (o == b)
    );

    // sel=10 routes c to o.
    check_sel_10_routes_c: assert property (
        @($global_clock) (sel == 2'b10) |-> (o == c)
    );

    // sel=11 routes d to o.
    check_sel_11_routes_d: assert property (
        @($global_clock) (sel == 2'b11) |-> (o == d)
    );

endmodule