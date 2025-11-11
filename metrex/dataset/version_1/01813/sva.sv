// SVA for mux_4to1. Bind into the DUT for structural access to internal nets.
module mux_4to1_sva;
  // Ignore checks while any input select/data is X/Z
  default disable iff ($isunknown({sel,in0,in1,in2,in3}));

  // Functional spec: out must equal the selected input combinationally
  a_func: assert property (@(sel or in0 or in1 or in2 or in3)
    out == ((sel==2'b00) ? in0 :
            (sel==2'b01) ? in1 :
            (sel==2'b10) ? in2 : in3));

  // Known-propagation: with all known inputs, output must be known
  a_known: assert property (@(sel or in0 or in1 or in2 or in3)
    !$isunknown({sel,in0,in1,in2,in3}) |-> !$isunknown(out));

  // Internal decode correctness and mutual exclusion
  a_sel0_def: assert property (@(sel)  sel0 == (~sel[1] & ~sel[0]));
  a_sel1_def: assert property (@(sel)  sel1 == (~sel[1] &  sel[0]));
  a_decode_mutex: assert property (@(sel) !(sel0 && sel1));

  // Non-interference and propagation on single-input change with stable select
  a_single_change: assert property (@(in0 or in1 or in2 or in3 or sel)
    $stable(sel) &&
    $onehot({$changed(in0), $changed(in1), $changed(in2), $changed(in3)})
    |-> ##0 (out == ((sel==2'b00)? in0 :
                     (sel==2'b01)? in1 :
                     (sel==2'b10)? in2 : in3)));

  // Functional coverage: exercise all select values
  c_sel_00: cover property (@(sel) sel==2'b00);
  c_sel_01: cover property (@(sel) sel==2'b01);
  c_sel_10: cover property (@(sel) sel==2'b10);
  c_sel_11: cover property (@(sel) sel==2'b11);

  // Path coverage: each selected input change propagates to out in the same cycle
  c_path0: cover property (@(in0 or sel) sel==2'b00 && $stable({in1,in2,in3,sel}) && $changed(in0) ##0 (out==in0));
  c_path1: cover property (@(in1 or sel) sel==2'b01 && $stable({in0,in2,in3,sel}) && $changed(in1) ##0 (out==in1));
  c_path2: cover property (@(in2 or sel) sel==2'b10 && $stable({in0,in1,in3,sel}) && $changed(in2) ##0 (out==in2));
  c_path3: cover property (@(in3 or sel) sel==2'b11 && $stable({in0,in1,in2,sel}) && $changed(in3) ##0 (out==in3));
endmodule

bind mux_4to1 mux_4to1_sva u_mux_4to1_sva();