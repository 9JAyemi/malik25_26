// SVA for top_module
module top_module_sva (
  input  logic [2:0] a,
  input  logic [2:0] b,
  input  logic       sel_b1,
  input  logic       sel_b2,          // unused by DUT; covered to ensure it toggles
  input  logic       out_always,      // scalar in DUT (LSB of selected vector)
  input  logic [2:0] out_or_reg,
  input  logic       out_or_logical,
  input  logic [5:0] out_not
);

  default clocking cb @(*); endclocking

  // Static width sanity (compile-time)
  initial begin
    assert ($bits(a)==3 && $bits(b)==3 &&
            $bits(out_or_reg)==3 && $bits(out_not)==6 &&
            $bits(out_always)==1 && $bits(out_or_logical)==1)
      else $error("Port width mismatch");
  end

  // Functional correctness (use ##0 to avoid NBA races)
  property p_mux_lsb;        ##0 (out_always     === (sel_b1 ? b : a)[0]); endproperty
  property p_or_bitwise;     ##0 (out_or_reg     === (a | b));              endproperty
  property p_or_logical;     ##0 (out_or_logical === ((|a) || (|b)));       endproperty
  property p_not_concat;     ##0 (out_not        === ~{a, b});              endproperty
  a_mux_lsb:        assert property (p_mux_lsb)    else $error("mux LSB mismatch");
  a_or_bitwise:     assert property (p_or_bitwise) else $error("bitwise OR mismatch");
  a_or_logical:     assert property (p_or_logical) else $error("logical OR mismatch");
  a_not_concat:     assert property (p_not_concat) else $error("invert concat mismatch");

  // Outputs must be fully known when driving inputs are known (independent of sel_b2)
  property p_known_outs;
    (!$isunknown({a,b,sel_b1})) |-> ##0 !$isunknown({out_always,out_or_reg,out_or_logical,out_not});
  endproperty
  a_known_outs: assert property (p_known_outs) else $error("Unknown on outputs with known driving inputs");

  // Coverage
  c_mux_a:         cover property (sel_b1==0 ##0 out_always===a[0]);
  c_mux_b:         cover property (sel_b1==1 ##0 out_always===b[0]);
  c_or_zero:       cover property ((a==3'b000 && b==3'b000) ##0 (out_or_logical==1'b0 && out_or_reg==3'b000));
  c_or_all_ones:   cover property (((a|b)==3'b111) ##0 out_or_logical==1'b1);
  c_not_all_zero:  cover property (({a,b}==6'b000000) ##0 out_not==6'b111111);
  c_not_all_ones:  cover property (({a,b}==6'b111111) ##0 out_not==6'b000000);
  c_sel_b2_tog:    cover property ($changed(sel_b2));

endmodule

// Bind into DUT
bind top_module top_module_sva sva_top_module (.*);