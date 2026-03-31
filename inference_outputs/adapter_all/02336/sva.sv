module MUX4_1_SL_sva (
    input logic [1:0] Sel,
    input logic [3:0] S0,
    input logic [3:0] S1,
    input logic [3:0] S2,
    input logic [3:0] S3,
    input logic [3:0] out
);
    // No clock/reset in RTL; combinational 4:1 mux; assertions sample on any input edge.

    // out equals the selected input per the mux equation.
    check_mux_function: assert property (
        @(posedge Sel[0] or negedge Sel[0] or posedge Sel[1] or negedge Sel[1] or
          posedge S0[0] or negedge S0[0] or posedge S0[1] or negedge S0[1] or posedge S0[2] or negedge S0[2] or posedge S0[3] or negedge S0[3] or
          posedge S1[0] or negedge S1[0] or posedge S1[1] or negedge S1[1] or posedge S1[2] or negedge S1[2] or posedge S1[3] or negedge S1[3] or
          posedge S2[0] or negedge S2[0] or posedge S2[1] or negedge S2[1] or posedge S2[2] or negedge S2[2] or posedge S2[3] or negedge S2[3] or
          posedge S3[0] or negedge S3[0] or posedge S3[1] or negedge S3[1] or posedge S3[2] or negedge S3[2] or posedge S3[3] or negedge S3[3] or
          posedge out[0] or negedge out[0] or posedge out[1] or negedge out[1] or posedge out[2] or negedge out[2] or posedge out[3] or negedge out[3])
        out == (Sel[1] ? (Sel[0] ? S3 : S2) : (Sel[0] ? S1 : S0))
    );

    // When Sel==2'b00, out equals S0.
    check_sel_00: assert property (
        @(posedge Sel[0] or negedge Sel[0] or posedge Sel[1] or negedge Sel[1] or
          posedge S0[0] or negedge S0[0] or posedge S0[1] or negedge S0[1] or posedge S0[2] or negedge S0[2] or posedge S0[3] or negedge S0[3] or
          posedge S1[0] or negedge S1[0] or posedge S1[1] or negedge S1[1] or posedge S1[2] or negedge S1[2] or posedge S1[3] or negedge S1[3] or
          posedge S2[0] or negedge S2[0] or posedge S2[1] or negedge S2[1] or posedge S2[2] or negedge S2[2] or posedge S2[3] or negedge S2[3] or
          posedge S3[0] or negedge S3[0] or posedge S3[1] or negedge S3[1] or posedge S3[2] or negedge S3[2] or posedge S3[3] or negedge S3[3] or
          posedge out[0] or negedge out[0] or posedge out[1] or negedge out[1] or posedge out[2] or negedge out[2] or posedge out[3] or negedge out[3])
        (Sel == 2'b00) |-> (out == S0)
    );

    // When Sel==2'b01, out equals S1.
    check_sel_01: assert property (
        @(posedge Sel[0] or negedge Sel[0] or posedge Sel[1] or negedge Sel[1] or
          posedge S0[0] or negedge S0[0] or posedge S0[1] or negedge S0[1] or posedge S0[2] or negedge S0[2] or posedge S0[3] or negedge S0[3] or
          posedge S1[0] or negedge S1[0] or posedge S1[1] or negedge S1[1] or posedge S1[2] or negedge S1[2] or posedge S1[3] or negedge S1[3] or
          posedge S2[0] or negedge S2[0] or posedge S2[1] or negedge S2[1] or posedge S2[2] or negedge S2[2] or posedge S2[3] or negedge S2[3] or
          posedge S3[0] or negedge S3[0] or posedge S3[1] or negedge S3[1] or posedge S3[2] or negedge S3[2] or posedge S3[3] or negedge S3[3] or
          posedge out[0] or negedge out[0] or posedge out[1] or negedge out[1] or posedge out[2] or negedge out[2] or posedge out[3] or negedge out[3])
        (Sel == 2'b01) |-> (out == S1)
    );

    // When Sel==2'b10, out equals S2.
    check_sel_10: assert property (
        @(posedge Sel[0] or negedge Sel[0] or posedge Sel[1] or negedge Sel[1] or
          posedge S0[0] or negedge S0[0] or posedge S0[1] or negedge S0[1] or posedge S0[2] or negedge S0[2] or posedge S0[3] or negedge S0[3] or
          posedge S1[0] or negedge S1[0] or posedge S1[1] or negedge S1[1] or posedge S1[2] or negedge S1[2] or posedge S1[3] or negedge S1[3] or
          posedge S2[0] or negedge S2[0] or posedge S2[1] or negedge S2[1] or posedge S2[2] or negedge S2[2] or posedge S2[3] or negedge S2[3] or
          posedge S3[0] or negedge S3[0] or posedge S3[1] or negedge S3[1] or posedge S3[2] or negedge S3[2] or posedge S3[3] or negedge S3[3] or
          posedge out[0] or negedge out[0] or posedge out[1] or negedge out[1] or posedge out[2] or negedge out[2] or posedge out[3] or negedge out[3])
        (Sel == 2'b10) |-> (out == S2)
    );

    // When Sel==2'b11, out equals S3.
    check_sel_11: assert property (
        @(posedge Sel[0] or negedge Sel[0] or posedge Sel[1] or negedge Sel[1] or
          posedge S0[0] or negedge S0[0] or posedge S0[1] or negedge S0[1] or posedge S0[2] or negedge S0[2] or posedge S0[3] or negedge S0[3] or
          posedge S1[0] or negedge S1[0] or posedge S1[1] or negedge S1[1] or posedge S1[2] or negedge S1[2] or posedge S1[3] or negedge S1[3] or
          posedge S2[0] or negedge S2[0] or posedge S2[1] or negedge S2[1] or posedge S2[2] or negedge S2[2] or posedge S2[3] or negedge S2[3] or
          posedge S3[0] or negedge S3[0] or posedge S3[1] or negedge S3[1] or posedge S3[2] or negedge S3[2] or posedge S3[3] or negedge S3[3] or
          posedge out[0] or negedge out[0] or posedge out[1] or negedge out[1] or posedge out[2]