module mux4_sva (
    input logic sel1,
    input logic sel0,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out
);
    ///// Functional mapping /////
    // When sel=00, out equals in0.
    check_map_00: assert property (
        @(posedge sel1 or negedge sel1 or posedge sel0 or negedge sel0 or
          posedge in0 or negedge in0 or posedge in1 or negedge in1 or
          posedge in2 or negedge in2 or posedge in3 or negedge in3 or
          posedge out or negedge out)
        ((sel1 == 1'b0) && (sel0 == 1'b0)) |-> (out == in0)
    );

    // When sel=01, out equals in1.
    check_map_01: assert property (
        @(posedge sel1 or negedge sel1 or posedge sel0 or negedge sel0 or
          posedge in0 or negedge in0 or posedge in1 or negedge in1 or
          posedge in2 or negedge in2 or posedge in3 or negedge in3 or
          posedge out or negedge out)
        ((sel1 == 1'b0) && (sel0 == 1'b1)) |-> (out == in1)
    );

    // When sel=10, out equals in2.
    check_map_10: assert property (
        @(posedge sel1 or negedge sel1 or posedge sel0 or negedge sel0 or
          posedge in0 or negedge in0 or posedge in1 or negedge in1 or
          posedge in2 or negedge in2 or posedge in3 or negedge in3 or
          posedge out or negedge out)
        ((sel1 == 1'b1) && (sel0 == 1'b0)) |-> (out == in2)
    );

    // When sel=11, out equals in3.
    check_map_11: assert property (
        @(posedge sel1 or negedge sel1 or posedge sel0 or negedge sel0 or
          posedge in0 or negedge in0 or posedge in1 or negedge in1 or
          posedge in2 or negedge in2 or posedge in3 or negedge in3 or
          posedge out or negedge out)
        ((sel1 == 1'b1) && (sel0 == 1'b1)) |-> (out == in3)
    );

    ///// Stability with selects and selected input held /////
    // If sel=00 and sel/in0 stable, out remains stable.
    hold_out_when_00_and_in0_stable: assert property (
        @(posedge sel1 or negedge sel1 or posedge sel0 or negedge sel0 or
          posedge in0 or negedge in0 or posedge in1 or negedge in1 or
          posedge in2 or negedge in2 or posedge in3 or negedge in3 or
          posedge out or negedge out)
        ((sel1 == 1'b0) && (sel0 == 1'b0) && $stable(sel1) && $stable(sel0) && $stable(in0)) |-> $stable(out)
    );

    // If sel=01 and sel/in1 stable, out remains stable.
    hold_out_when_01_and_in1_stable: assert property (
        @(posedge sel1 or negedge sel1 or posedge sel0 or negedge sel0 or
          posedge in0 or negedge in0 or posedge in1 or negedge in1 or
          posedge in2 or negedge in2 or posedge in3 or negedge in3 or
          posedge out or negedge out)
        ((sel1 == 1'b0) && (sel0 == 1'b1) && $stable(sel1) && $stable(sel0) && $stable(in1)) |-> $stable(out)
    );

    // If sel=10 and sel/in2 stable, out remains stable.
    hold_out_when_10_and_in2_stable: assert property (
        @(posedge sel1 or negedge sel1 or posedge sel0 or negedge sel0 or
          posedge in0 or negedge in0 or posedge in1 or negedge in1 or
          posedge in2 or negedge in2 or posedge in3 or negedge in3 or
          posedge out or negedge out)
        ((sel1 == 1'b1) && (sel0 == 1'b0) && $stable(sel1) && $stable(sel0) && $stable(in2)) |-> $stable(out)
    );

    // If sel=11 and sel/in3 stable, out remains stable.
    hold_out_when_11_and_in3_stable: assert property (
        @(posedge sel1 or negedge sel1 or posedge sel0 or negedge sel0 or
          posedge in0 or negedge in0 or posedge in1 or negedge in1 or
          posedge in2 or negedge in2 or posedge in3 or negedge in3 or
          posedge out or negedge out)
        ((sel1 == 1'b1) && (sel0 == 1'b1) && $stable(sel1) && $stable(sel0) && $stable(in3)) |-> $stable(out)
    );

    ///// Out changes only when selected input changes (with selects held) /////
    // If sel=00 held and out changes, in0 must have changed.
    out_change_implies_in0_change_when_00: assert property (
        @(posedge sel1 or negedge sel1 or posedge sel0 or negedge sel0 or
          posedge in0 or negedge in0 or posedge in1 or negedge in1 or
          posedge in2 or negedge in2 or posedge in3 or negedge in3 or
          posedge out or negedge out)
        ((sel1 == 1'b0) && (sel0 == 1'b0) && $stable(sel1) && $stable(sel0) && $changed(out)) |-> $changed(in0)
    );

    // If sel=01 held and out changes, in1 must have changed.
    out_change_implies_in1_change_when_01: assert property (
        @(posedge sel1 or negedge sel1 or posedge sel0 or negedge sel0 or
          posedge in0 or negedge in0 or posedge in1 or negedge in1 or
          posedge in2 or negedge in2 or posedge in3 or negedge in3 or
          posedge out or negedge out)
        ((sel1 == 1'b0) && (sel0 == 1'b1) && $stable(sel1) && $stable(sel0) && $changed(out)) |-> $changed(in1)
    );

    // If sel=10 held and out changes, in2 must have changed.
    out_change_implies_in2_change_when_10: assert property (
        @(posedge sel1 or negedge sel1 or posedge sel0 or negedge sel0 or
          posedge in0 or negedge in0 or posedge in1 or negedge in1 or
          posedge in2 or negedge in2 or posedge in3 or negedge in3 or
          posedge out or negedge out)
        ((sel1 == 1'b1) && (sel0 == 1'b0) && $stable(sel1) && $stable(sel0) && $changed(out)) |-> $changed(in2)
    );

    // If sel=11 held and out changes, in3 must have changed.
    out_change_implies_in3_change_when_11: assert property (
        @(posedge sel1 or negedge sel1 or posedge sel0 or negedge sel0 or
          posedge in0 or negedge in0 or posedge in1 or negedge in1 or
          posedge in2 or negedge in2 or posedge in3 or negedge in3 or
          posedge out or negedge out)
        ((sel1 == 1'b1) && (sel0 == 1'b1) && $stable(sel1) && $stable(sel0) && $changed(out)) |-> $changed(in3)
    );
endmodule