// SVA checker for mux32bits_32to1
// Provide a verification clock 'clk' from the testbench.
module mux32bits_32to1_sva #(parameter bit EN_X_CHECK = 1) (
  input  logic        clk,
  input  logic [4:0]  s,
  input  logic [31:0] i31, i30, i29, i28, i27, i26, i25, i24,
                      i23, i22, i21, i20, i19, i18, i17, i16,
                      i15, i14, i13, i12, i11, i10, i9,  i8,
                      i7,  i6,  i5,  i4,  i3,  i2,  i1,  i0,
  input  logic [31:0] z
);
  default clocking cb @(posedge clk); endclocking

  // Pack inputs into an array for concise checks
  logic [31:0] in [0:31];
  assign in[0]=i0;  assign in[1]=i1;  assign in[2]=i2;  assign in[3]=i3;
  assign in[4]=i4;  assign in[5]=i5;  assign in[6]=i6;  assign in[7]=i7;
  assign in[8]=i8;  assign in[9]=i9;  assign in[10]=i10;assign in[11]=i11;
  assign in[12]=i12;assign in[13]=i13;assign in[14]=i14;assign in[15]=i15;
  assign in[16]=i16;assign in[17]=i17;assign in[18]=i18;assign in[19]=i19;
  assign in[20]=i20;assign in[21]=i21;assign in[22]=i22;assign in[23]=i23;
  assign in[24]=i24;assign in[25]=i25;assign in[26]=i26;assign in[27]=i27;
  assign in[28]=i28;assign in[29]=i29;assign in[30]=i30;assign in[31]=i31;

  // Functional correctness against the DUT’s case-encoding
  // s==0 -> z==0; s in [1..31] -> z == in[s-1] (note: i31 is never selected by this DUT)
  ap_sel_range:  assert property ( (s inside {[5'd1:5'd31]}) |-> (z == in[s-1]) );
  ap_sel_zero:   assert property ( (s == 5'd0) |-> (z == 32'h0) );

  // Combinational stability: if select and all inputs are stable, output is stable
  ap_stable:     assert property ( $stable({s,
                                           i0, i1, i2, i3, i4, i5, i6, i7,
                                           i8, i9, i10,i11,i12,i13,i14,i15,
                                           i16,i17,i18,i19,i20,i21,i22,i23,
                                           i24,i25,i26,i27,i28,i29,i30,i31})
                                   |-> $stable(z) );

  // Known-value checks (optional)
  generate if (EN_X_CHECK) begin
    ap_no_x_s:   assert property ( !$isunknown(s) )
                  else $error("mux32bits_32to1: s has X/Z");
    ap_known_z:  assert property ( (!$isunknown({s,
                                                i0, i1, i2, i3, i4, i5, i6, i7,
                                                i8, i9, i10,i11,i12,i13,i14,i15,
                                                i16,i17,i18,i19,i20,i21,i22,i23,
                                                i24,i25,i26,i27,i28,i29,i30,i31}))
                                   |-> !$isunknown(z) )
                  else $error("mux32bits_32to1: z unknown with known inputs/select");
  end endgenerate

  // Functional coverage: hit every selection and the default
  genvar k;
  generate
    for (k=1; k<=31; k++) begin : COV_SEL
      cp_sel: cover property ( (s == k) && (z == in[k-1]) );
    end
  endgenerate
  cp_default: cover property ( (s == 5'd0) && (z == 32'h0) );

endmodule

// Bind example (provide a clock visible in the bind scope, e.g., tb.clk)
// bind mux32bits_32to1 mux32bits_32to1_sva sva ( .clk(tb.clk),
//   .s(s), .i31(i31), .i30(i30), .i29(i29), .i28(i28), .i27(i27), .i26(i26), .i25(i25), .i24(i24),
//   .i23(i23), .i22(i22), .i21(i21), .i20(i20), .i19(i19), .i18(i18), .i17(i17), .i16(i16),
//   .i15(i15), .i14(i14), .i13(i13), .i12(i12), .i11(i11), .i10(i10), .i9(i9), .i8(i8),
//   .i7(i7), .i6(i6), .i5(i5), .i4(i4), .i3(i3), .i2(i2), .i1(i1), .i0(i0), .z(z) );