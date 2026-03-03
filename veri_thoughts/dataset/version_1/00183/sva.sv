// SVA checker for complement_module
module complement_module_sva (
  input  logic [3:0] in_vec,
  input  logic       sel_comp,
  input  logic [3:0] outv,
  input  logic [3:0] complement
);

  // Functional correctness (delta-cycle settle with ##0)
  property p_func_direct;
    @(in_vec or sel_comp)
      !$isunknown({in_vec, sel_comp})
      |-> ##0 ( outv == in_vec
             && complement == (sel_comp ? (~in_vec + 4'b0001) : ~in_vec) );
  endproperty
  assert property (p_func_direct)
    else $error("Functional mismatch: outv/complement incorrect for inputs");

  // Independent arithmetic invariants
  property p_sum_mode0;
    @(in_vec or sel_comp)
      (!$isunknown({in_vec, sel_comp}) && !sel_comp)
      |-> ##0 ((in_vec + complement) == 4'hF);
  endproperty
  assert property (p_sum_mode0)
    else $error("Mode0: in_vec + complement != 0xF");

  property p_sum_mode1;
    @(in_vec or sel_comp)
      (!$isunknown({in_vec, sel_comp}) && sel_comp)
      |-> ##0 ((in_vec + complement) == 4'h0);
  endproperty
  assert property (p_sum_mode1)
    else $error("Mode1: in_vec + complement != 0x0 (mod 16)");

  // No X/Z on outputs when inputs are known
  property p_no_x_out_when_inputs_known;
    @(in_vec or sel_comp)
      !$isunknown({in_vec, sel_comp})
      |-> ##0 (! $isunknown({outv, complement}));
  endproperty
  assert property (p_no_x_out_when_inputs_known)
    else $error("Outputs contain X/Z while inputs are known");

  // Coverage
  // - Full cross coverage of sel_comp and all in_vec values
  covergroup cg_complements @(in_vec or sel_comp);
    c_sel: coverpoint sel_comp { bins b0 = {0}; bins b1 = {1}; }
    c_in : coverpoint in_vec   { bins all[] = {[4'h0:4'hF]}; }
    cross c_sel, c_in;
  endgroup
  cg_complements cg_inst = new();

  // - Toggle coverage on sel_comp
  cover property (@(sel_comp) (sel_comp==0) ##1 (sel_comp==1));
  cover property (@(sel_comp) (sel_comp==1) ##1 (sel_comp==0));

  // - Corner value coverage with functional result observed
  cover property (@(in_vec or sel_comp)
                  (!sel_comp && in_vec inside {4'h0,4'hF}) ##0 ((in_vec + complement)==4'hF));
  cover property (@(in_vec or sel_comp)
                  ( sel_comp && in_vec inside {4'h0,4'h1,4'h8,4'hF}) ##0 ((in_vec + complement)==4'h0));

endmodule

// Bind into the DUT
bind complement_module complement_module_sva sva_i (
  .in_vec(in_vec),
  .sel_comp(sel_comp),
  .outv(outv),
  .complement(complement)
);