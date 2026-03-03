// SVA bind file for top_module hierarchy

// Top-level monitor
module top_sva_mon (input a, input b, input sel_b1, input sel_b2, input out_always);
  // Evaluate after any input edge, avoiding race via ##0
  property p_top_func_known;
    @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
      ##0 (!$isunknown({a,b,sel_b1,sel_b2})) |->
          (out_always === ((a & b) ^ ((sel_b1 & sel_b2) ? b : a)) && !$isunknown(out_always));
  endproperty
  assert property (p_top_func_known);

  // out_always must equal internal final_out wire
  property p_out_connect;
    @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
      ##0 (out_always === final_out);
  endproperty
  assert property (p_out_connect);

  // Mux select formation: sel into mux is sel_b1 & sel_b2
  property p_mux_sel_form;
    @(posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
      ##0 (mux_inst.sel === (sel_b1 & sel_b2));
  endproperty
  assert property (p_mux_sel_form);

  // Functional coverage: exercise both mux paths through to out_always
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
                  ##0 ((sel_b1 & sel_b2)==0 && out_always === ((a & b) ^ a)));
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
                  ##0 ((sel_b1 & sel_b2)==1 && out_always === ((a & b) ^ b)));
endmodule

// and_gate monitor
module and_gate_sva_mon (input a, input b, input out);
  property p_and;
    @(posedge a or negedge a or posedge b or negedge b) ##0 (out === (a & b));
  endproperty
  assert property (p_and);

  property p_and_known;
    @(posedge a or negedge a or posedge b or negedge b) ##0 (!$isunknown({a,b})) |->
                                                         (!$isunknown(out));
  endproperty
  assert property (p_and_known);

  cover property (@(posedge a or negedge a or posedge b or negedge b) ##0 out==0);
  cover property (@(posedge a or negedge a or posedge b or negedge b) ##0 out==1);
endmodule

// mux_2to1 monitor
module mux_2to1_sva_mon (input a, input b, input sel, input out);
  property p_mux;
    @(posedge a or negedge a or posedge b or negedge b or posedge sel or negedge sel) ##0 (out === (sel ? b : a));
  endproperty
  assert property (p_mux);

  property p_mux_known;
    @(posedge a or negedge a or posedge b or negedge b or posedge sel or negedge sel) ##0 (!$isunknown({a,b,sel})) |->
                                                                                      (!$isunknown(out));
  endproperty
  assert property (p_mux_known);

  // Path coverage
  cover property (@(posedge sel or negedge sel or posedge a or negedge a or posedge b or negedge b) ##0 (sel==0 && out==a));
  cover property (@(posedge sel or negedge sel or posedge a or negedge a or posedge b or negedge b) ##0 (sel==1 && out==b));
endmodule

// functional_module monitor
module functional_module_sva_mon (input and_out, input mux_out, input final_out);
  property p_xor;
    @(posedge and_out or negedge and_out or posedge mux_out or negedge mux_out) ##0 (final_out === (and_out ^ mux_out));
  endproperty
  assert property (p_xor);

  property p_xor_known;
    @(posedge and_out or negedge and_out or posedge mux_out or negedge mux_out) ##0 (!$isunknown({and_out,mux_out})) |->
                                                                                 (!$isunknown(final_out));
  endproperty
  assert property (p_xor_known);

  // Truth-table coverage
  cover property (@(posedge and_out or negedge and_out or posedge mux_out or negedge mux_out) ##0 (and_out==0 && mux_out==0 && final_out==0));
  cover property (@(posedge and_out or negedge and_out or posedge mux_out or negedge mux_out) ##0 (and_out==0 && mux_out==1 && final_out==1));
  cover property (@(posedge and_out or negedge and_out or posedge mux_out or negedge mux_out) ##0 (and_out==1 && mux_out==0 && final_out==1));
  cover property (@(posedge and_out or negedge and_out or posedge mux_out or negedge mux_out) ##0 (and_out==1 && mux_out==1 && final_out==0));
endmodule

// Bind the monitors
bind top_module        top_sva_mon                top_sva_b(.a(a), .b(b), .sel_b1(sel_b1), .sel_b2(sel_b2), .out_always(out_always));
bind and_gate          and_gate_sva_mon           and_sva_b(.a(a), .b(b), .out(out));
bind mux_2to1          mux_2to1_sva_mon           mux_sva_b(.a(a), .b(b), .sel(sel), .out(out));
bind functional_module functional_module_sva_mon  func_sva_b(.and_out(and_out), .mux_out(mux_out), .final_out(final_out));