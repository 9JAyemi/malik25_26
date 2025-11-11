// SVA checkers (bind into DUT). Concise, focused on functional correctness and key independence/coverage.

//////////////////////////////
// and_gate_mux_not checker //
//////////////////////////////
module and_gate_mux_not_sva;
  // Functional correctness (when inputs known)
  // out = a ? in : ~in; not_in = ~in
  always_comb begin
    if (!$isunknown({a,in})) begin
      assert (out == (a ? in : ~in)) else $error("and_gate_mux_not: out mismatch");
      assert (not_in == ~in)        else $error("and_gate_mux_not: not_in mismatch");
    end
  end

  // b has no effect on out when a,in stable
  assert property (@(posedge b or negedge b)
                     $stable(a) && $stable(in) && !$isunknown({a,in,out})
                   |-> $stable(out))
    else $error("and_gate_mux_not: b affected out");

  // Coverage: both mux branches seen
  cover property (@(posedge a) 1);
  cover property (@(negedge a) 1);
endmodule

bind and_gate_mux_not and_gate_mux_not_sva and_gate_mux_not_sva_i();


////////////////////////////
// priority_encoder checker
////////////////////////////
module priority_encoder_sva;
  // Basic combinational correctness (when inputs known)
  always_comb begin
    if (!$isunknown(in)) begin
      assert (inv_in == ~in) else $error("priority_encoder: inv_in mismatch");
      assert (and_out == in) else $error("priority_encoder: and_out != in");
      // pos truncation behavior: pos == {1'b0, in[7], in[6]}
      assert (pos == {1'b0, in[7], in[6]})
        else $error("priority_encoder: pos mismatch");
    end
  end

  // Lower bits [5:0] must not affect pos
  genvar k;
  generate
    for (k=0; k<6; k++) begin: g_noeffect_lowbits
      assert property (@(posedge in[k] or negedge in[k])
                         $stable(in[7:6]) && !$isunknown({in[7:6],pos})
                       |-> $stable(pos))
        else $error("priority_encoder: in[%0d] affected pos", k);
    end
  endgenerate

  // Coverage: all combinations of in[7:6]
  cover property (@(in[7] or in[6]) in[7:6]==2'b00);
  cover property (@(in[7] or in[6]) in[7:6]==2'b01);
  cover property (@(in[7] or in[6]) in[7:6]==2'b10);
  cover property (@(in[7] or in[6]) in[7:6]==2'b11);
endmodule

bind priority_encoder priority_encoder_sva priority_encoder_sva_i();


/////////////////////////
// final_module checker
/////////////////////////
module final_module_sva;
  // Local expressions for readability in assertions
  function automatic logic exp_and(input logic a_i, input logic in0);
    exp_and = a_i ? in0 : ~in0;
  endfunction
  function automatic logic [2:0] exp_pri(input logic [7:0] in_i);
    exp_pri = {1'b0, in_i[7], in_i[6]};
  endfunction

  // Check internal composition and final output (when inputs known)
  always_comb begin
    if (!$isunknown({a,in})) begin
      assert (and_out == exp_and(a, in[0]))
        else $error("final_module: and_out mismatch");
      assert (priority_pos == exp_pri(in))
        else $error("final_module: priority_pos mismatch");
      assert (pos == (and_out ? priority_pos : 3'b000))
        else $error("final_module: pos mismatch");
    end
  end

  // b has no effect on pos when a,in stable
  assert property (@(posedge b or negedge b)
                     $stable(a) && $stable(in) && !$isunknown({a,in,pos})
                   |-> $stable(pos))
    else $error("final_module: b affected pos");

  // Coverage: gate off and gate on with various priority outputs
  cover property (@(in[0] or a) (exp_and(a,in[0])==1'b0));
  cover property (@(in[0] or a or in[7] or in[6])
                  (exp_and(a,in[0])==1'b1) && (exp_pri(in)==3'b000));
  cover property (@(in[0] or a or in[7] or in[6])
                  (exp_and(a,in[0])==1'b1) && (exp_pri(in)==3'b001));
  cover property (@(in[0] or a or in[7] or in[6])
                  (exp_and(a,in[0])==1'b1) && (exp_pri(in)==3'b010));
  cover property (@(in[0] or a or in[7] or in[6])
                  (exp_and(a,in[0])==1'b1) && (exp_pri(in)==3'b011));
endmodule

bind final_module final_module_sva final_module_sva_i();