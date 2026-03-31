module udp_mux_4to1_sva (
    input logic [3:0] out,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel
);
    // Combinational 4:1 mux with no clock/reset; assertions sample on any input edge.

    // When sel==00, out selects in0.
    check_sel00_selects_in0: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1] or
          posedge in0[0] or negedge in0[0] or posedge in0[1] or negedge in0[1] or
          posedge in0[2] or negedge in0[2] or posedge in0[3] or negedge in0[3] or
          posedge in1[0] or negedge in1[0] or posedge in1[1] or negedge in1[1] or
          posedge in1[2] or negedge in1[2] or posedge in1[3] or negedge in1[3] or
          posedge in2[0] or negedge in2[0] or posedge in2[1] or negedge in2[1] or
          posedge in2[2] or negedge in2[2] or posedge in2[3] or negedge in2[3] or
          posedge in3[0] or negedge in3[0] or posedge in3[1] or negedge in3[1] or
          posedge in3[2] or negedge in3[2] or posedge in3[3] or negedge in3[3])
        (sel == 2'b00) |-> (out == in0)
    );

    // When sel==01, out selects in1.
    check_sel01_selects_in1: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1] or
          posedge in0[0] or negedge in0[0] or posedge in0[1] or negedge in0[1] or
          posedge in0[2] or negedge in0[2] or posedge in0[3] or negedge in0[3] or
          posedge in1[0] or negedge in1[0] or posedge in1[1] or negedge in1[1] or
          posedge in1[2] or negedge in1[2] or posedge in1[3] or negedge in1[3] or
          posedge in2[0] or negedge in2[0] or posedge in2[1] or negedge in2[1] or
          posedge in2[2] or negedge in2[2] or posedge in2[3] or negedge in2[3] or
          posedge in3[0] or negedge in3[0] or posedge in3[1] or negedge in3[1] or
          posedge in3[2] or negedge in3[2] or posedge in3[3] or negedge in3[3])
        (sel == 2'b01) |-> (out == in1)
    );

    // When sel==10, out selects in2.
    check_sel10_selects_in2: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1] or
          posedge in0[0] or negedge in0[0] or posedge in0[1] or negedge in0[1] or
          posedge in0[2] or negedge in0[2] or posedge in0[3] or negedge in0[3] or
          posedge in1[0] or negedge in1[0] or posedge in1[1] or negedge in1[1] or
          posedge in1[2] or negedge in1[2] or posedge in1[3] or negedge in1[3] or
          posedge in2[0] or negedge in2[0] or posedge in2[1] or negedge in2[1] or
          posedge in2[2] or negedge in2[2] or posedge in2[3] or negedge in2[3] or
          posedge in3[0] or negedge in3[0] or posedge in3[1] or negedge in3[1] or
          posedge in3[2] or negedge in3[2] or posedge in3[3] or negedge in3[3])
        (sel == 2'b10) |-> (out == in2)
    );

    // When sel==11, out selects in3.
    check_sel11_selects_in3: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1] or
          posedge in0[0] or negedge in0[0] or posedge in0[1] or negedge in0[1] or
          posedge in0[2] or negedge in0[2] or posedge in0[3] or negedge in0[3] or
          posedge in1[0] or negedge in1[0] or posedge in1[1] or negedge in1[1] or
          posedge in1[2] or negedge in1[2] or posedge in1[3] or negedge in1[3] or
          posedge in2[0] or negedge in2[0] or posedge in2[1] or negedge in2[1] or
          posedge in2[2] or negedge in2[2] or posedge in2[3] or negedge in2[3] or
          posedge in3[0] or negedge in3[0] or posedge in3[1] or negedge in3[1] or
          posedge in3[2] or negedge in3[2] or posedge in3[3] or negedge in3[3])
        (sel == 2'b11) |-> (out == in3)
    );

    // If sel and all inputs are stable, out must be stable.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1] or
          posedge in0[0] or negedge in0[0] or posedge in0[1] or negedge in0[1] or
          posedge in0[2] or negedge in0[2] or posedge in0[3] or negedge in0[3] or
          posedge in1[0] or negedge in1[0] or posedge in1[1] or negedge in1[1] or
          posedge in1[2] or negedge in1[2] or posedge in1[3] or negedge in1[3] or
          posedge in2[0] or negedge in2[0] or posedge in2[1] or negedge in2[1] or
          posedge in2[2] or negedge in2[2] or posedge in2[3] or negedge in2[3] or
          posedge in3[0] or negedge in3[0] or posedge in3[1] or negedge in3[1] or
          posedge in3[2] or negedge in3[2] or posedge in3[3] or negedge in3[3])
        $stable(sel) && $stable(in0) && $stable(in1) && $stable(in2) && $stable(in3) |-> $stable(out)
    );

    // If sel==00 and in0 is stable, out must be stable.
    check_sel00_out_stable_when_in0_stable: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1] or
          posedge in0[0] or negedge in0[0] or posedge in0[1] or negedge in0[1] or
          posedge in0[2] or negedge in0[2] or posedge in0[3] or negedge in0[3] or
          posedge in1[0] or negedge in1[0] or posedge in1[1] or negedge in1[1] or
          posedge in1[2] or negedge in1[2] or posedge in1[3] or negedge in1