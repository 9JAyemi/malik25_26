module mux4_sva (
    input logic clk,          // sampling clock for assertions
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic [1:0] sel,
    input logic out
);
    // Out equals the mux function for all sel values.
    check_mux_function: assert property (
        @(posedge clk) out == (sel[1] ? (sel[0] ? in4 : in3) : (sel[0] ? in2 : in1))
    );

    // When sel==2'b00, out follows in1.
    check_sel00_routes_in1: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == in1)
    );

    // When sel==2'b01, out follows in2.
    check_sel01_routes_in2: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == in2)
    );

    // When sel==2'b10, out follows in3.
    check_sel10_routes_in3: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == in3)
    );

    // When sel==2'b11, out follows in4.
    check_sel11_routes_in4: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == in4)
    );

    // When sel[1]==0, out selects between in1/in2 by sel[0].
    check_msb0_selects_low_pair: assert property (
        @(posedge clk) (!sel[1]) |-> (out == (sel[0] ? in2 : in1))
    );

    // When sel[1]==1, out selects between in3/in4 by sel[0].
    check_msb1_selects_high_pair: assert property (
        @(posedge clk) (sel[1]) |-> (out == (sel[0] ? in4 : in3))
    );
endmodule