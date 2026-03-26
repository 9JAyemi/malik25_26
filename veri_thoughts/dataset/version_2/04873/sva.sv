module mux_4to1_assertions (
    input logic clk,
    input logic [1:0] sel,
    input logic [3:0] in,
    input logic out
);

    // sel=00 routes in[0] to out.
    check_sel_00_routes_in0: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == in[0])
    );

    // sel=01 routes in[1] to out.
    check_sel_01_routes_in1: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == in[1])
    );

    // sel=10 routes in[2] to out.
    check_sel_10_routes_in2: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == in[2])
    );

    // sel=11 routes in[3] to out.
    check_sel_11_routes_in3: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == in[3])
    );

    // With sel held at 00, a stable in[0] keeps out stable.
    check_sel_00_stable_selected_input_holds_output: assert property (
        @(posedge clk) (sel == 2'b00) && $stable(sel) && $stable(in[0]) |-> $stable(out)
    );

    // With sel held at 01, a stable in[1] keeps out stable.
    check_sel_01_stable_selected_input_holds_output: assert property (
        @(posedge clk) (sel == 2'b01) && $stable(sel) && $stable(in[1]) |-> $stable(out)
    );

    // With sel held at 10, a stable in[2] keeps out stable.
    check_sel_10_stable_selected_input_holds_output: assert property (
        @(posedge clk) (sel == 2'b10) && $stable(sel) && $stable(in[2]) |-> $stable(out)
    );

    // With sel held at 11, a stable in[3] keeps out stable.
    check_sel_11_stable_selected_input_holds_output: assert property (
        @(posedge clk) (sel == 2'b11) && $stable(sel) && $stable(in[3]) |-> $stable(out)
    );

endmodule