module mux_4to1_assertions (
    input logic       clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic [3:0] out
);

    // sel=00 routes in0 to out.
    check_sel_00_routes_in0: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == in0)
    );

    // sel=01 routes in1 to out.
    check_sel_01_routes_in1: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == in1)
    );

    // sel=10 routes in2 to out.
    check_sel_10_routes_in2: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == in2)
    );

    // sel=11 routes in3 to out.
    check_sel_11_routes_in3: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == in3)
    );

    // With sel=00 held and in0 stable, out stays stable.
    check_sel_00_stable_input_keeps_out_stable: assert property (
        @(posedge clk) (!$initstate && $stable(sel) && (sel == 2'b00) && $stable(in0)) |-> $stable(out)
    );

    // With sel=01 held and in1 stable, out stays stable.
    check_sel_01_stable_input_keeps_out_stable: assert property (
        @(posedge clk) (!$initstate && $stable(sel) && (sel == 2'b01) && $stable(in1)) |-> $stable(out)
    );

    // With sel=10 held and in2 stable, out stays stable.
    check_sel_10_stable_input_keeps_out_stable: assert property (
        @(posedge clk) (!$initstate && $stable(sel) && (sel == 2'b10) && $stable(in2)) |-> $stable(out)
    );

    // With sel=11 held and in3 stable, out stays stable.
    check_sel_11_stable_input_keeps_out_stable: assert property (
        @(posedge clk) (!$initstate && $stable(sel) && (sel == 2'b11) && $stable(in3)) |-> $stable(out)
    );

    // If all inputs and sel are stable, out stays stable.
    check_all_stable_keeps_out_stable: assert property (
        @(posedge clk) (!$initstate && $stable(sel) && $stable(in0) && $stable(in1) && $stable(in2) && $stable(in3)) |-> $stable(out)
    );

endmodule