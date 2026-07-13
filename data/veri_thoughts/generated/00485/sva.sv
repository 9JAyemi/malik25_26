module mux4to1_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic [1:0] sel,
    input logic y
);

    // sel=00 routes a to y.
    check_sel_00_routes_a: assert property (
        @($global_clock) disable iff (1'b0)
        (sel == 2'b00) |-> (y == a)
    );

    // sel=01 routes b to y.
    check_sel_01_routes_b: assert property (
        @($global_clock) disable iff (1'b0)
        (sel == 2'b01) |-> (y == b)
    );

    // sel=10 routes c to y.
    check_sel_10_routes_c: assert property (
        @($global_clock) disable iff (1'b0)
        (sel == 2'b10) |-> (y == c)
    );

    // sel=11 routes d to y.
    check_sel_11_routes_d: assert property (
        @($global_clock) disable iff (1'b0)
        (sel == 2'b11) |-> (y == d)
    );

    // y always matches the mux equation.
    check_mux_equation: assert property (
        @($global_clock) disable iff (1'b0)
        y == ((sel[1] & sel[0]) ? d :
              ((sel[1] & ~sel[0]) ? c :
               ((~sel[1] & sel[0]) ? b : a)))
    );

endmodule