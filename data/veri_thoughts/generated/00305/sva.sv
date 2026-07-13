module mux_4to1_and_assertions (
    input logic       clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] c,
    input logic [3:0] d,
    input logic [1:0] sel,
    input logic [3:0] y
);

    // y matches the cascaded 4-to-1 mux equation implemented in the RTL.
    check_full_mux_equation: assert property (
        @(posedge clk)
        y === (sel[1] ? (sel[0] ? d : c) : (sel[0] ? b : a))
    );

    // When the upper select is low, y comes from the a/b mux path.
    check_sel1_low_uses_ab_path: assert property (
        @(posedge clk)
        (sel[1] === 1'b0) |-> (y === (sel[0] ? b : a))
    );

    // When the upper select is high, y comes from the c/d mux path.
    check_sel1_high_uses_cd_path: assert property (
        @(posedge clk)
        (sel[1] === 1'b1) |-> (y === (sel[0] ? d : c))
    );

    // sel=00 routes input a to y.
    check_sel_00_routes_a: assert property (
        @(posedge clk)
        (sel === 2'b00) |-> (y === a)
    );

    // sel=01 routes input b to y.
    check_sel_01_routes_b: assert property (
        @(posedge clk)
        (sel === 2'b01) |-> (y === b)
    );

    // sel=10 routes input c to y.
    check_sel_10_routes_c: assert property (
        @(posedge clk)
        (sel === 2'b10) |-> (y === c)
    );

    // sel=11 routes input d to y.
    check_sel_11_routes_d: assert property (
        @(posedge clk)
        (sel === 2'b11) |-> (y === d)
    );

endmodule