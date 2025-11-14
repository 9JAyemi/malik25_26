// SVA for tkg_c3/C3
// synthesis translate_off

// Bind module for C3: checks internal structure and function
module C3_sva (input logic o, i0, i1, i2,
               input logic a, b, c, d, e);

  default clocking cb @(*); endclocking

  // Functional equivalence (majority-of-3)
  assert property ((!$isunknown({i0,i1,i2})) |-> (o == ((i0 & i1) | (i0 & i2) | (i1 & i2))));

  // Check gate-level decomposition
  assert property ((!$isunknown({i0,i1})) |-> (a == (i0 & i1)));
  assert property ((!$isunknown({i0,i2})) |-> (b == (i0 & i2)));
  assert property ((!$isunknown({i1,i2})) |-> (c == (i1 & i2)));
  assert property ((!$isunknown({a,b}))     |-> (d == (a | b)));
  assert property ((!$isunknown({d,c}))     |-> (e == (d | c)));
  assert property ((!$isunknown({e}))       |-> (o == e));

  // Toggle coverage on output
  cover property (!$isunknown(o) && $rose(o));
  cover property (!$isunknown(o) && $fell(o));

  // Functional coverage: 0/1/2/3 ones on inputs
  cover property ((!$isunknown({i0,i1,i2})) &&
                  ((i0?1:0)+(i1?1:0)+(i2?1:0) == 0) && !o);
  cover property ((!$isunknown({i0,i1,i2})) &&
                  ((i0?1:0)+(i1?1:0)+(i2?1:0) == 1) && !o);
  cover property ((!$isunknown({i0,i1,i2})) &&
                  ((i0?1:0)+(i1?1:0)+(i2?1:0) == 2) &&  o);
  cover property ((!$isunknown({i0,i1,i2})) &&
                  ((i0?1:0)+(i1?1:0)+(i2?1:0) == 3) &&  o);
endmodule

bind C3 C3_sva c3_sva_inst (.*);

// Optional: simple wrapper-level functional check
module tkg_c3_sva (input logic o, i0, i1, i2);
  default clocking @(*); endclocking
  assert property ((!$isunknown({i0,i1,i2})) |-> (o == ((i0 & i1) | (i0 & i2) | (i1 & i2))));
endmodule

bind tkg_c3 tkg_c3_sva tkg_c3_sva_inst (.*);

// synthesis translate_on