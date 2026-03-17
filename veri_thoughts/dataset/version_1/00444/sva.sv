module mux_4to1_sva (
    input logic clk,
    input logic out,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic [1:0] sel
);

    // Output matches the implemented gate-level mux equation.
    check_out_matches_mux_equation: assert property (
        @(posedge clk)
        out == ((in0 & ~sel[0] & ~sel[1]) |
                (in1 &  sel[0] & ~sel[1]) |
                (in2 & ~sel[0] &  sel[1]) |
                (in3 &  sel[0] &  sel[1]))
    );

    // Select value 00 routes in0 to the output.
    check_sel_00_routes_in0: assert property (
        @(posedge clk)
        (sel == 2'b00) |-> (out == in0)
    );

    // Select value 01 routes in1 to the output.
    check_sel_01_routes_in1: assert property (
        @(posedge clk)
        (sel == 2'b01) |-> (out == in1)
    );

    // Select value 10 routes in2 to the output.
    check_sel_10_routes_in2: assert property (
        @(posedge clk)
        (sel == 2'b10) |-> (out == in2)
    );

    // Select value 11 routes in3 to the output.
    check_sel_11_routes_in3: assert property (
        @(posedge clk)
        (sel == 2'b11) |-> (out == in3)
    );

    // If all inputs and select stay constant, the output stays constant.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk)
        ($stable(sel) && $stable(in0) && $stable(in1) && $stable(in2) && $stable(in3)) |-> $stable(out)
    );

endmodule