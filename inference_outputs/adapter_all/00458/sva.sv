module mux4to1_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic [1:0] sel,
    input logic out
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

    // With sel[0] low, the upper mux selects the low-input path.
    check_sel0_low_selects_low_path: assert property (
        @(posedge clk) (sel[0] == 1'b0) |-> (out == (sel[1] ? in2 : in0))
    );

    // With sel[0] high, the upper mux selects the high-input path.
    check_sel0_high_selects_high_path: assert property (
        @(posedge clk) (sel[0] == 1'b1) |-> (out == (sel[1] ? in3 : in1))
    );

    // With sel[1] low, the final mux selects the low-input path.
    check_sel1_low_selects_low_path: assert property (
        @(posedge clk) (sel[1] == 1'b0) |-> (out == (sel[0] ? in1 : in0))
    );

    // With sel[1] high, the final mux selects the high-input path.
    check_sel1_high_selects_high_path: assert property (
        @(posedge clk) (sel[1] == 1'b1) |-> (out == (sel[0] ? in3 : in2))
    );

endmodule