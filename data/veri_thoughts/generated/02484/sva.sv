module Mux8_sva #(
    parameter data_width = 8
) (
    // Sampling clock (RTL has no clock/reset; pure combinational; use CLK only for assertion sampling)
    input  logic                         CLK,

    // DUT ports
    input  logic [2:0]                   sel,
    input  logic [data_width-1:0]        i0,
    input  logic [data_width-1:0]        i1,
    input  logic [data_width-1:0]        i2,
    input  logic [data_width-1:0]        i3,
    input  logic [data_width-1:0]        i4,
    input  logic [data_width-1:0]        i5,
    input  logic [data_width-1:0]        i6,
    input  logic [data_width-1:0]        i7,
    input  logic [data_width-1:0]        o
);

    ///// Functional mapping /////
    // Output equals the data selected by sel (pure combinational mux behavior).
    check_mux_function: assert property (
        @(posedge CLK) o == (
            (sel == 3'd0) ? i0 :
            (sel == 3'd1) ? i1 :
            (sel == 3'd2) ? i2 :
            (sel == 3'd3) ? i3 :
            (sel == 3'd4) ? i4 :
            (sel == 3'd5) ? i5 :
            (sel == 3'd6) ? i6 : i7
        )
    );

    ///// Stability guarantees /////
    // With sel=0 held and i0 stable, o remains stable.
    stable_sel0_i0: assert property (
        @(posedge CLK) (sel == 3'd0 && $stable(sel) && $stable(i0)) |-> $stable(o)
    );
    // With sel=1 held and i1 stable, o remains stable.
    stable_sel1_i1: assert property (
        @(posedge CLK) (sel == 3'd1 && $stable(sel) && $stable(i1)) |-> $stable(o)
    );
    // With sel=2 held and i2 stable, o remains stable.
    stable_sel2_i2: assert property (
        @(posedge CLK) (sel == 3'd2 && $stable(sel) && $stable(i2)) |-> $stable(o)
    );
    // With sel=3 held and i3 stable, o remains stable.
    stable_sel3_i3: assert property (
        @(posedge CLK) (sel == 3'd3 && $stable(sel) && $stable(i3)) |-> $stable(o)
    );
    // With sel=4 held and i4 stable, o remains stable.
    stable_sel4_i4: assert property (
        @(posedge CLK) (sel == 3'd4 && $stable(sel) && $stable(i4)) |-> $stable(o)
    );
    // With sel=5 held and i5 stable, o remains stable.
    stable_sel5_i5: assert property (
        @(posedge CLK) (sel == 3'd5 && $stable(sel) && $stable(i5)) |-> $stable(o)
    );
    // With sel=6 held and i6 stable, o remains stable.
    stable_sel6_i6: assert property (
        @(posedge CLK) (sel == 3'd6 && $stable(sel) && $stable(i6)) |-> $stable(o)
    );
    // With sel=7 held and i7 stable, o remains stable.
    stable_sel7_i7: assert property (
        @(posedge CLK) (sel == 3'd7 && $stable(sel) && $stable(i7)) |-> $stable(o)
    );

    ///// Change sensitivity /////
    // o changes only if sel changes or the currently selected input changes.
    check_o_change_causes: assert property (
        @(posedge CLK) $changed(o) |-> (
            $changed(sel) ||
            ((sel == 3'd0) && $changed(i0)) ||
            ((sel == 3'd1) && $changed(i1)) ||
            ((sel == 3'd2) && $changed(i2)) ||
            ((sel == 3'd3) && $changed(i3)) ||
            ((sel == 3'd4) && $changed(i4)) ||
            ((sel == 3'd5) && $changed(i5)) ||
            ((sel == 3'd6) && $changed(i6)) ||
            ((sel == 3'd7) && $changed(i7))
        )
    );

endmodule