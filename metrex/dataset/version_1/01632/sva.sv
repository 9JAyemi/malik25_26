// SVA for top_module — concise, high-quality checks and coverage

module top_module_sva (
  input logic a, b, c, d,
  input logic xor1_out, xor2_out,
  input logic out_func
);

  // Internal XORs must match inputs (use ##0 to avoid preponed sampling race)
  property p_xors_correct;
    @(a or b or c or d) disable iff ($isunknown({a,b,c,d}))
      1'b1 |-> ##0 (xor1_out == (a ^ b) && xor2_out == (c ^ d));
  endproperty
  assert property (p_xors_correct);

  // Output must equal OR of internal XORs and direct expression
  property p_out_correct;
    @(a or b or c or d or xor1_out or xor2_out)
      disable iff ($isunknown({a,b,c,d,xor1_out,xor2_out}))
      1'b1 |-> ##0 (out_func == (xor1_out | xor2_out) &&
                    out_func == ((a ^ b) | (c ^ d)));
  endproperty
  assert property (p_out_correct);

  // Output not X when inputs are known
  assert property (@(a or b or c or d)
                   disable iff ($isunknown({a,b,c,d}))
                   1'b1 |-> ##0 !$isunknown(out_func));

  // Truth table coverage of (a^b, c^d)
  cover property (@(a or b or c or d)
                  disable iff ($isunknown({a,b,c,d}))
                  ##0 ((a^b)==0 && (c^d)==0 && out_func==0));
  cover property (@(a or b or c or d)
                  disable iff ($isunknown({a,b,c,d}))
                  ##0 ((a^b)==1 && (c^d)==0 && out_func==1));
  cover property (@(a or b or c or d)
                  disable iff ($isunknown({a,b,c,d}))
                  ##0 ((a^b)==0 && (c^d)==1 && out_func==1));
  cover property (@(a or b or c or d)
                  disable iff ($isunknown({a,b,c,d}))
                  ##0 ((a^b)==1 && (c^d)==1 && out_func==1));

  // Output toggle coverage
  cover property (@(a or b or c or d)
                  disable iff ($isunknown({a,b,c,d}))
                  ##0 $rose(out_func));
  cover property (@(a or b or c or d)
                  disable iff ($isunknown({a,b,c,d}))
                  ##0 $fell(out_func));

endmodule

bind top_module top_module_sva u_top_module_sva (
  .a(a), .b(b), .c(c), .d(d),
  .xor1_out(xor1_out), .xor2_out(xor2_out),
  .out_func(out_func)
);