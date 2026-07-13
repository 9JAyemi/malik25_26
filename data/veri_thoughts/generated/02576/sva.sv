module top_module_sva (
    input  logic        a,
    input  logic        b,
    input  logic [2:0]  sel,
    input  logic [3:0]  data0,
    input  logic [3:0]  data1,
    input  logic [3:0]  data2,
    input  logic [3:0]  data3,
    input  logic [3:0]  data4,
    input  logic [3:0]  data5,
    input  logic        clk,
    input  logic [3:0]  out
);
    // Clock: clk; no reset in RTL. Mixed logic: combinational mux/2's-comp + registered out.

    function automatic logic [3:0] mux_sel (
        input logic [2:0] s,
        input logic [3:0] d0, d1, d2, d3, d4, d5
    );
        case (s)
            3'b000: mux_sel = d0;
            3'b001: mux_sel = d1;
            3'b010: mux_sel = d2;
            3'b011: mux_sel = d3;
            3'b100: mux_sel = d4;
            3'b101: mux_sel = d5;
            default: mux_sel = 4'b0001;
        endcase
    endfunction

    ///// Registered output function /////
    // Out equals prior-cycle selected data or its 2's complement when a&b=1.
    check_out_matches_spec: assert property (
        @(posedge clk)
            $past(1'b1) |-> out ==
                ( ($past(a) & $past(b))
                  ? ((~mux_sel($past(sel), $past(data0), $past(data1), $past(data2), $past(data3), $past(data4), $past(data5))) + 4'b0001)
                  :   mux_sel($past(sel), $past(data0), $past(data1), $past(data2), $past(data3), $past(data4), $past(data5))
                )
    );

    ///// Mux select passthrough cases when a&b=0 /////
    // sel=000 passes data0 when a&b=0.
    check_sel0_passthrough: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel)==3'b000) && !($past(a)&$past(b)) |-> out == $past(data0)
    );
    // sel=001 passes data1 when a&b=0.
    check_sel1_passthrough: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel)==3'b001) && !($past(a)&$past(b)) |-> out == $past(data1)
    );
    // sel=010 passes data2 when a&b=0.
    check_sel2_passthrough: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel)==3'b010) && !($past(a)&$past(b)) |-> out == $past(data2)
    );
    // sel=011 passes data3 when a&b=0.
    check_sel3_passthrough: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel)==3'b011) && !($past(a)&$past(b)) |-> out == $past(data3)
    );
    // sel=100 passes data4 when a&b=0.
    check_sel4_passthrough: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel)==3'b100) && !($past(a)&$past(b)) |-> out == $past(data4)
    );
    // sel=101 passes data5 when a&b=0.
    check_sel5_passthrough: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel)==3'b101) && !($past(a)&$past(b)) |-> out == $past(data5)
    );

    ///// Mux select two's-complement cases when a&b=1 /////
    // sel=000 outputs ~data0+1 when a&b=1.
    check_sel0_twoscomp: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel)==3'b000) && ($past(a)&$past(b)) |-> out == ((~$past(data0)) + 4'b0001)
    );
    // sel=001 outputs ~data1+1 when a&b=1.
    check_sel1_twoscomp: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel)==3'b001) && ($past(a)&$past(b)) |-> out == ((~$past(data1)) + 4'b0001)
    );
    // sel=010 outputs ~data2+1 when a&b=1.
    check_sel2_twoscomp: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel)==3'b010) && ($past(a)&$past(b)) |-> out == ((~$past(data2)) + 4'b0001)
    );
    // sel=011 outputs ~data3+1 when a&b=1.
    check_sel3_twoscomp: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel)==3'b011) && ($past(a)&$past(b)) |-> out == ((~$past(data3)) + 4'b0001)
    );
    // sel=100 outputs ~data4+1 when a&b=1.
    check_sel4_twoscomp: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel)==3'b100) && ($past(a)&$past(b)) |-> out == ((~$past(data4)) + 4'b0001)
    );
    // sel=101 outputs ~data5+1 when a&b=1.
    check_sel5_twoscomp: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel)==3'b101) && ($past(a)&$past(b)) |-> out == ((~$past(data5)) + 4'b0001)
    );

    ///// Default mux behavior for invalid selects (110/111) /////
    // Invalid sel outputs 0001 when a&b=0.
    check_default_sel_passthrough: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel) inside {3'b110,3'b111}) && !($past(a)&$past(b)) |-> out == 4'b0001
    );
    // Invalid sel outputs 1111 (2's comp of 0001) when a&b=1.
    check_default_sel_twoscomp: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel) inside {3'b110,3'b111}) && ($past(a)&$past(b)) |-> out == 4'b1111
    );

endmodule