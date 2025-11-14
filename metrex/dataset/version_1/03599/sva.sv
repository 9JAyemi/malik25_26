// SVA checker for my_module
module my_module_sva;
  // Sample on any input edge; allow 0-delay settle with ##0
  default clocking cb @(
    posedge g or negedge g or
    posedge p or negedge p or
    posedge g_prec or negedge g_prec or
    posedge p_prec or negedge p_prec
  ); endclocking

  // Functional equivalence checks
  property p_logic;  ##0 (p_out == (p & p_prec)); endproperty
  property g_logic;  ##0 (g_out == (p & (g_prec | ~g))); endproperty
  property aoi_eq;   ##0 (n5    == ~((g_prec & p) | ((~g) & p))); endproperty
  property inv_link; ##0 (g_out == ~n5); endproperty

  assert property(p_logic);
  assert property(g_logic);
  assert property(aoi_eq);
  assert property(inv_link);

  // No unknowns on outputs when inputs are known
  assert property( (!$isunknown({g,p,g_prec,p_prec})) |-> ##0 !$isunknown({g_out,p_out,n5}) );

  // Targeted functional coverage
  cover property( ##0 (!p && g_out==0 && p_out==0) );                  // p=0 path
  cover property( ##0 ( p && g_prec && g_out) );                       // p=1, g_prec=1 -> g_out=1
  cover property( ##0 ( p && !g_prec && !g && g_out) );                // p=1, g_prec=0, g=0 -> g_out=1
  cover property( ##0 ( p && !g_prec &&  g && !g_out) );               // p=1, g_prec=0, g=1 -> g_out=0
  cover property( ##0 ( p &&  p_prec && p_out) );                      // p_out=1 case
  cover property( ##0 ( p && !p_prec && !p_out) );                     // p_out=0 with p=1

  // Toggle coverage on inputs and outputs
  cover property($rose(g));     cover property($fell(g));
  cover property($rose(p));     cover property($fell(p));
  cover property($rose(g_prec));cover property($fell(g_prec));
  cover property($rose(p_prec));cover property($fell(p_prec));
  cover property($rose(g_out)); cover property($fell(g_out));
  cover property($rose(p_out)); cover property($fell(p_out));
endmodule

// Bind into DUT
bind my_module my_module_sva sva_inst();