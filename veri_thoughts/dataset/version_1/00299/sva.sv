module mux4_reset_assertions (
    input logic       clk,
    input logic       reset,
    input logic [1:0] sel,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [3:0] out
);

    // Reset forces the output to zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) reset |-> (out == 4'b0000)
    );

    // When not in reset and sel is 00, out matches in0.
    check_sel_00_routes_in0: assert property (
        @(posedge clk) disable iff (reset) (sel == 2'b00) |-> (out == in0)
    );

    // When not in reset and sel is 01, out matches in1.
    check_sel_01_routes_in1: assert property (
        @(posedge clk) disable iff (reset) (sel == 2'b01) |-> (out == in1)
    );

    // When not in reset and sel is 10, out matches in2.
    check_sel_10_routes_in2: assert property (
        @(posedge clk) disable iff (reset) (sel == 2'b10) |-> (out == in2)
    );

    // When not in reset and sel is 11, out matches in3.
    check_sel_11_routes_in3: assert property (
        @(posedge clk) disable iff (reset) (sel == 2'b11) |-> (out == in3)
    );

endmodule