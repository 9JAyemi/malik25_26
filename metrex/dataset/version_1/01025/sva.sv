// SVA checkers and binds for the given design
// Focused, concise, and covering functionality and key corner cases.

module nand_gate_sva;
  // Functional check
  property p_func; out === ~(a & b); endproperty
  assert property (@(posedge a or negedge a or posedge b or negedge b) p_func)
    else $error("nand_gate mismatch: out=%b a=%b b=%b", out, a, b);

  // Truth-table coverage
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==0 && out==1));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==1 && out==1));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==0 && out==1));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==1 && out==0));
endmodule

module nor_gate_sva;
  // Functional check
  property p_func; out === ~(a | b); endproperty
  assert property (@(posedge a or negedge a or posedge b or negedge b) p_func)
    else $error("nor_gate mismatch: out=%b a=%b b=%b", out, a, b);

  // Truth-table coverage
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==0 && out==1));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==1 && out==0));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==0 && out==0));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==1 && out==0));
endmodule

module xnor_gate_sva;
  // Structural checks on internals
  property p_nand_int; nand_out === ~(a & b); endproperty
  property p_nor_int;  nor_out  === ~(a | b); endproperty
  property p_out_str;  out      === ~(nand_out & nor_out); endproperty
  assert property (@(posedge a or negedge a or posedge b or negedge b) p_nand_int)
    else $error("xnor_gate.nand_out mismatch: a=%b b=%b nand_out=%b", a, b, nand_out);
  assert property (@(posedge a or negedge a or posedge b or negedge b) p_nor_int)
    else $error("xnor_gate.nor_out mismatch: a=%b b=%b nor_out=%b", a, b, nor_out);
  assert property (@(posedge a or negedge a or posedge b or negedge b) p_out_str)
    else $error("xnor_gate out structural mismatch");

  // Functional equivalence of composed logic (simplifies to OR)
  property p_func; out === (a | b); endproperty
  assert property (@(posedge a or negedge a or posedge b or negedge b) p_func)
    else $error("xnor_gate functional mismatch: out=%b a=%b b=%b", out, a, b);

  // Truth-table coverage for effective OR
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==0 && out==0));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==1 && out==1));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==0 && out==1));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==1 && out==1));
endmodule

module top_module_sva;
  // Structural checks on intermediates
  property p_x1; xnor_out1 === (in[0] | in[1]); endproperty
  property p_x2; xnor_out2 === (in[2] | in[3]); endproperty
  property p_out_str; out === (xnor_out1 | xnor_out2); endproperty
  assert property (@(posedge in[0] or negedge in[0] or
                     posedge in[1] or negedge in[1] or
                     posedge in[2] or negedge in[2] or
                     posedge in[3] or negedge in[3]) p_x1)
    else $error("top: xnor_out1 mismatch");
  assert property (@(posedge in[0] or negedge in[0] or
                     posedge in[1] or negedge in[1] or
                     posedge in[2] or negedge in[2] or
                     posedge in[3] or negedge in[3]) p_x2)
    else $error("top: xnor_out2 mismatch");
  assert property (@(posedge in[0] or negedge in[0] or
                     posedge in[1] or negedge in[1] or
                     posedge in[2] or negedge in[2] or
                     posedge in[3] or negedge in[3]) p_out_str)
    else $error("top: out structural mismatch");

  // Functional reduction-OR of all inputs
  property p_func; out === (|in); endproperty
  assert property (@(posedge in[0] or negedge in[0] or
                     posedge in[1] or negedge in[1] or
                     posedge in[2] or negedge in[2] or
                     posedge in[3] or negedge in[3]) p_func)
    else $error("top: out != |in (out=%b in=%b)", out, in);

  // Corner-case and distribution coverage
  cover property (@(posedge in[0] or negedge in[0] or
                    posedge in[1] or negedge in[1] or
                    posedge in[2] or negedge in[2] or
                    posedge in[3] or negedge in[3]) ($countones(in)==0 && out==0));
  cover property (@(posedge in[0] or negedge in[0] or
                    posedge in[1] or negedge in[1] or
                    posedge in[2] or negedge in[2] or
                    posedge in[3] or negedge in[3]) ($countones(in)==1 && out==1));
  cover property (@(posedge in[0] or negedge in[0] or
                    posedge in[1] or negedge in[1] or
                    posedge in[2] or negedge in[2] or
                    posedge in[3] or negedge in[3]) ($countones(in)==2 && out==1));
  cover property (@(posedge in[0] or negedge in[0] or
                    posedge in[1] or negedge in[1] or
                    posedge in[2] or negedge in[2] or
                    posedge in[3] or negedge in[3]) ($countones(in)==3 && out==1));
  cover property (@(posedge in[0] or negedge in[0] or
                    posedge in[1] or negedge in[1] or
                    posedge in[2] or negedge in[2] or
                    posedge in[3] or negedge in[3]) ($countones(in)==4 && out==1));

  // Toggle coverage for each input and output
  genvar i;
  generate
    for (i=0;i<4;i++) begin : g_in_tog
      cover property (@(posedge in[i]) 1);
      cover property (@(negedge in[i]) 1);
    end
  endgenerate
  cover property (@(posedge out) 1);
  cover property (@(negedge out) 1);
endmodule

// Bind checkers into DUT scopes
bind nand_gate  nand_gate_sva  nand_gate_sva_i();
bind nor_gate   nor_gate_sva   nor_gate_sva_i();
bind xnor_gate  xnor_gate_sva  xnor_gate_sva_i();
bind top_module top_module_sva top_module_sva_i();