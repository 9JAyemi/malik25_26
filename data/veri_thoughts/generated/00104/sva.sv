module mux_4to2_sva (
    input logic       clk,
    input logic       in0,
    input logic       in1,
    input logic       in2,
    input logic       in3,
    input logic [1:0] sel,
    input logic [1:0] out
);

    // The low output bit is always driven low.
    check_out_lsb_zero: assert property (
        @(posedge clk) out[0] == 1'b0
    );

    // sel=00 routes in0 to the high output bit.
    check_sel_00_routes_in0: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == {in0, 1'b0})
    );

    // sel=01 routes in1 to the high output bit.
    check_sel_01_routes_in1: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == {in1, 1'b0})
    );

    // sel=10 routes in2 to the high output bit.
    check_sel_10_routes_in2: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == {in2, 1'b0})
    );

    // sel=11 routes in3 to the high output bit.
    check_sel_11_routes_in3: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == {in3, 1'b0})
    );

endmodule