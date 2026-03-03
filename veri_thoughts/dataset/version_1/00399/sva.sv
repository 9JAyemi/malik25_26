// SVA checkers for simple combinational DUTs.
// Use ##0 to sample after combinational updates.

//////////////////// f1_test ////////////////////
module f1_test_sva(input in, input out);
  // Functional equivalence
  ap_f1_eq: assert property (@(in or out) 1 |-> ##0 (out === in));

  // Coverage
  cp_f1_val0:  cover  property (@(in) ##0 (in==1'b0 && out==1'b0));
  cp_f1_val1:  cover  property (@(in) ##0 (in==1'b1 && out==1'b1));
  cp_f1_tgl:   cover  property (@(in) $changed(in) ##0 $changed(out));
endmodule
bind f1_test f1_test_sva f1_test_sva_i(.in(in), .out(out));


//////////////////// f2_test ////////////////////
module f2_test_sva(input in, input out);
  // Functional inversion
  ap_f2_inv: assert property (@(in or out) 1 |-> ##0 (out === ~in));

  // Coverage
  cp_f2_in0:  cover property (@(in) ##0 (in==1'b0 && out==1'b1));
  cp_f2_in1:  cover property (@(in) ##0 (in==1'b1 && out==1'b0));
  cp_f2_tgl:  cover property (@(in) $changed(in) ##0 $changed(out));
endmodule
bind f2_test f2_test_sva f2_test_sva_i(.in(in), .out(out));


//////////////////// f3_test ////////////////////
module f3_test_sva(input [1:0] in, input select, input out);
  // Functional mux
  ap_f3_mux: assert property (@(in or select or out)
                              1 |-> ##0 (out === (select ? in[1] : in[0])));

  // Stability: if select and selected input stable, out must be stable
  ap_f3_stable: assert property (@(in or select or out)
                                 ($stable(select) && $stable(select ? in[1] : in[0]))
                                 |-> ##0 $stable(out));

  // Coverage: both selects and both output values
  cp_f3_sel0: cover property (@(select) (select==1'b0));
  cp_f3_sel1: cover property (@(select) (select==1'b1));
  cp_f3_out0: cover property (@(in or select) ##0 (out==1'b0));
  cp_f3_out1: cover property (@(in or select) ##0 (out==1'b1));
endmodule
bind f3_test f3_test_sva f3_test_sva_i(.in(in), .select(select), .out(out));


//////////////////// f4_test ////////////////////
module f4_test_sva(input [127:0] in, input [6:0] select, input out);
  // Functional wide mux
  ap_f4_mux: assert property (@(in or select or out)
                              1 |-> ##0 (out === in[select]));

  // Stability: if select and selected bit stable, out stable
  ap_f4_stable: assert property (@(in or select or out)
                                 ($stable(select) && $stable(in[select]))
                                 |-> ##0 $stable(out));

  // Coverage: hit all select values 0..127
  genvar i;
  generate
    for (i=0; i<128; i++) begin : gen_cp_sel
      cp_f4_sel: cover property (@(select) (select==i[6:0]));
    end
  endgenerate

  // Coverage: observe both output values
  cp_f4_out0: cover property (@(in or select) ##0 (out==1'b0));
  cp_f4_out1: cover property (@(in or select) ##0 (out==1'b1));
endmodule
bind f4_test f4_test_sva f4_test_sva_i(.in(in), .select(select), .out(out));


//////////////////// f5_test ////////////////////
module f5_test_sva(input [7:0] in, input [2:0] select, input out);
  // Functional 8:1 mux
  ap_f5_mux: assert property (@(in or select or out)
                              1 |-> ##0 (out === in[select]));

  // Stability: if select and selected bit stable, out stable
  ap_f5_stable: assert property (@(in or select or out)
                                 ($stable(select) && $stable(in[select]))
                                 |-> ##0 $stable(out));

  // Coverage: hit all select values 0..7
  genvar j;
  generate
    for (j=0; j<8; j++) begin : gen_cp_sel
      cp_f5_sel: cover property (@(select) (select==j[2:0]));
    end
  endgenerate

  // Coverage: observe both output values
  cp_f5_out0: cover property (@(in or select) ##0 (out==1'b0));
  cp_f5_out1: cover property (@(in or select) ##0 (out==1'b1));
endmodule
bind f5_test f5_test_sva f5_test_sva_i(.in(in), .select(select), .out(out));