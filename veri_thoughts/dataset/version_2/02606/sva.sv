module mux16_sva #(
    parameter W = 1
) (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] sel,
    input logic [W-1:0]
        i1111,
        i1110,
        i1101,
        i1100,
        i1011,
        i1010,
        i1001,
        i1000,
        i0111,
        i0110,
        i0101,
        i0100,
        i0011,
        i0010,
        i0001,
        i0000,
    input logic [W-1:0] o
);

    ///// 16:1 mux selection mapping /////
    // When sel==0, output equals i0000.
    sel_0_maps_to_i0000: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd0) |-> (o == i0000)
    );
    // When sel==1, output equals i0001.
    sel_1_maps_to_i0001: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd1) |-> (o == i0001)
    );
    // When sel==2, output equals i0010.
    sel_2_maps_to_i0010: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd2) |-> (o == i0010)
    );
    // When sel==3, output equals i0011.
    sel_3_maps_to_i0011: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd3) |-> (o == i0011)
    );
    // When sel==4, output equals i0100.
    sel_4_maps_to_i0100: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd4) |-> (o == i0100)
    );
    // When sel==5, output equals i0101.
    sel_5_maps_to_i0101: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd5) |-> (o == i0101)
    );
    // When sel==6, output equals i0110.
    sel_6_maps_to_i0110: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd6) |-> (o == i0110)
    );
    // When sel==7, output equals i0111.
    sel_7_maps_to_i0111: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd7) |-> (o == i0111)
    );
    // When sel==8, output equals i1000.
    sel_8_maps_to_i1000: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd8) |-> (o == i1000)
    );
    // When sel==9, output equals i1001.
    sel_9_maps_to_i1001: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd9) |-> (o == i1001)
    );
    // When sel==10, output equals i1010.
    sel_10_maps_to_i1010: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd10) |-> (o == i1010)
    );
    // When sel==11, output equals i1011.
    sel_11_maps_to_i1011: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd11) |-> (o == i1011)
    );
    // When sel==12, output equals i1100.
    sel_12_maps_to_i1100: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd12) |-> (o == i1100)
    );
    // When sel==13, output equals i1101.
    sel_13_maps_to_i1101: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd13) |-> (o == i1101)
    );
    // When sel==14, output equals i1110.
    sel_14_maps_to_i1110: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd14) |-> (o == i1110)
    );
    // When sel==15, output equals i1111 (default case).
    sel_15_maps_to_i1111: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 4'd15) |-> (o == i1111)
    );

    ///// Combinational stability /////
    // If sel and all inputs are stable over a cycle, o is stable too.
    stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn)
            $stable(sel) &&
            $stable(i0000) && $stable(i0001) && $stable(i0010) && $stable(i0011) &&
            $stable(i0100) && $stable(i0101) && $stable(i0110) && $stable(i0111) &&
            $stable(i1000) && $stable(i1001) && $stable(i1010) && $stable(i1011) &&
            $stable(i1100) && $stable(i1101) && $stable(i1110) && $stable(i1111)
            |-> $stable(o)
    );

endmodule