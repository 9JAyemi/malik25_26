module MUXn_8_1_sva #(
    parameter int MuxLen = 63
) (
    input logic [MuxLen:0] mux_in0,
    input logic [MuxLen:0] mux_in1,
    input logic [MuxLen:0] mux_in2,
    input logic [MuxLen:0] mux_in3,
    input logic [MuxLen:0] mux_in4,
    input logic [MuxLen:0] mux_in5,
    input logic [MuxLen:0] mux_in6,
    input logic [MuxLen:0] mux_in7,
    input logic [2:0]      mux_sel,
    input logic [MuxLen:0] mux_out
);
    // Combinational DUT with no clock/reset; use posedge mux_sel[0] as assertion clock; no reset (disable iff(1'b0)).

    // sel=000 routes mux_in0 to mux_out.
    select_000_routes_in0: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel == 3'b000) |-> (mux_out == mux_in0)
    );
    // sel=001 routes mux_in1 to mux_out.
    select_001_routes_in1: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel == 3'b001) |-> (mux_out == mux_in1)
    );
    // sel=010 routes mux_in2 to mux_out.
    select_010_routes_in2: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel == 3'b010) |-> (mux_out == mux_in2)
    );
    // sel=011 routes mux_in3 to mux_out.
    select_011_routes_in3: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel == 3'b011) |-> (mux_out == mux_in3)
    );
    // sel=100 routes mux_in4 to mux_out.
    select_100_routes_in4: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel == 3'b100) |-> (mux_out == mux_in4)
    );
    // sel=101 routes mux_in5 to mux_out.
    select_101_routes_in5: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel == 3'b101) |-> (mux_out == mux_in5)
    );
    // sel=110 routes mux_in6 to mux_out.
    select_110_routes_in6: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel == 3'b110) |-> (mux_out == mux_in6)
    );
    // sel=111 routes mux_in7 to mux_out.
    select_111_routes_in7: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel == 3'b111) |-> (mux_out == mux_in7)
    );

    // When high bits select {in0,in1} and in0==in1, output equals that value regardless of LSB.
    lsb_independence_grp0: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel[2:1] == 2'b00) && (mux_in0 == mux_in1) |-> (mux_out == mux_in0)
    );
    // When high bits select {in2,in3} and in2==in3, output equals that value regardless of LSB.
    lsb_independence_grp1: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel[2:1] == 2'b01) && (mux_in2 == mux_in3) |-> (mux_out == mux_in2)
    );
    // When high bits select {in4,in5} and in4==in5, output equals that value regardless of LSB.
    lsb_independence_grp2: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel[2:1] == 2'b10) && (mux_in4 == mux_in5) |-> (mux_out == mux_in4)
    );
    // When high bits select {in6,in7} and in6==in7, output equals that value regardless of LSB.
    lsb_independence_grp3: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel[2:1] == 2'b11) && (mux_in6 == mux_in7) |-> (mux_out == mux_in6)
    );

    // When low bits select index 0 and in0==in4, output equals that value regardless of MSB.
    msb_independence_idx0: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel[1:0] == 2'b00) && (mux_in0 == mux_in4) |-> (mux_out == mux_in0)
    );
    // When low bits select index 1 and in1==in5, output equals that value regardless of MSB.
    msb_independence_idx1: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel[1:0] == 2'b01) && (mux_in1 == mux_in5) |-> (mux_out == mux_in1)
    );
    // When low bits select index 2 and in2==in6, output equals that value regardless of MSB.
    msb_independence_idx2: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel[1:0] == 2'b10) && (mux_in2 == mux_in6) |-> (mux_out == mux_in2)
    );
    // When low bits select index 3 and in3==in7, output equals that value regardless of MSB.
    msb_independence_idx3: assert property (
        @(posedge mux_sel[0]) disable iff (1'b0) (mux_sel[1:0] == 2'b11) && (mux_in3 == mux_in7) |-> (mux_out == mux_in3)
    );
endmodule