module mux4to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic [3:0] out
);
    // When sel==00, out equals in0.
    check_sel00_maps_in0: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b00) |-> (out == in0)
    );

    // When sel==01, out equals in1.
    check_sel01_maps_in1: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b01) |-> (out == in1)
    );

    // When sel==10, out equals in2.
    check_sel10_maps_in2: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b10) |-> (out == in2)
    );

    // When sel==11, out equals in3.
    check_sel11_maps_in3: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b11) |-> (out == in3)
    );

    // If sel and all inputs are stable, out remains stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        $stable(sel) && $stable(in0) && $stable(in1) && $stable(in2) && $stable(in3) |-> $stable(out)
    );

    // If sel==00 and only in0 changes, out changes to match.
    check_out_follows_in0_when_sel00: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b00) && $stable(sel) && $stable(in1) && $stable(in2) && $stable(in3) && $changed(in0) |-> $changed(out)
    );

    // If sel==01 and only in1 changes, out changes to match.
    check_out_follows_in1_when_sel01: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b01) && $stable(sel) && $stable(in0) && $stable(in2) && $stable(in3) && $changed(in1) |-> $changed(out)
    );

    // If sel==10 and only in2 changes, out changes to match.
    check_out_follows_in2_when_sel10: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b10) && $stable(sel) && $stable(in0) && $stable(in1) && $stable(in3) && $changed(in2) |-> $changed(out)
    );

    // If sel==11 and only in3 changes, out changes to match.
    check_out_follows_in3_when_sel11: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b11) && $stable(sel) && $stable(in0) && $stable(in1) && $stable(in2) && $changed(in3) |-> $changed(out)
    );

    // If sel and in0 change while others are stable, out equals in0.
    check_out_when_sel00_and_in0_changes: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b00) && $changed(sel) && $changed(in0) && $stable(in1) && $stable(in2) && $stable(in3) |-> (out == in0)
    );
endmodule