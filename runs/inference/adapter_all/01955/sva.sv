module mux4to1_32_sva (
    input logic        clk,
    input logic [1:0]  sel,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] c,
    input logic [31:0] d,
    input logic [31:0] o
);

    // sel=00 routes a to o.
    check_sel_00_routes_a: assert property (
        @(posedge clk) (sel == 2'b00) |-> (o == a)
    );

    // sel=01 routes b to o.
    check_sel_01_routes_b: assert property (
        @(posedge clk) (sel == 2'b01) |-> (o == b)
    );

    // sel=10 routes c to o.
    check_sel_10_routes_c: assert property (
        @(posedge clk) (sel == 2'b10) |-> (o == c)
    );

    // sel=11 routes d to o.
    check_sel_11_routes_d: assert property (
        @(posedge clk) (sel == 2'b11) |-> (o == d)
    );

    // With sel=00 held and a stable, o remains stable.
    check_sel_00_stable_when_a_stable: assert property (
        @(posedge clk) (sel == 2'b00 && $stable(sel) && $stable(a)) |-> $stable(o)
    );

    // With sel=01 held and b stable, o remains stable.
    check_sel_01_stable_when_b_stable: assert property (
        @(posedge clk) (sel == 2'b01 && $stable(sel) && $stable(b)) |-> $stable(o)
    );

    // With sel=10 held and c stable, o remains stable.
    check_sel_10_stable_when_c_stable: assert property (
        @(posedge clk) (sel == 2'b10 && $stable(sel) && $stable(c)) |-> $stable(o)
    );

    // With sel=11 held and d stable, o remains stable.
    check_sel_11_stable_when_d_stable: assert property (
        @(posedge clk) (sel == 2'b11 && $stable(sel) && $stable(d)) |-> $stable(o)
    );

    // With sel=00 held and a changing, o changes.
    check_sel_00_change_reflects_a_change: assert property (
        @(posedge clk) (sel == 2'b00 && $stable(sel) && $changed(a)) |-> $changed(o)
    );

    // With sel=01 held and b changing, o changes.
    check_sel_01_change_reflects_b_change: assert property (
        @(posedge clk) (sel == 2'b01 && $stable(sel) && $changed(b)) |-> $changed(o)
    );

    // With sel=10 held and c changing, o changes.
    check_sel_10_change_reflects_c_change: assert property (
        @(posedge clk) (sel == 2'b10 && $stable(sel) && $changed(c)) |-> $changed(o)
    );

    // With sel=11 held and d changing, o changes.
    check_sel_11_change_reflects_d_change: assert property (
        @(posedge clk) (sel == 2'b11 && $stable(sel) && $changed(d)) |-> $changed(o)
    );

endmodule