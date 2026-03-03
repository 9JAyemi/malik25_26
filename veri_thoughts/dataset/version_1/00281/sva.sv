// SVA for mult_gate. Bind this to the DUT.
// Focus: functional equivalence, X-propagation guard, dominance implications, and compact but thorough coverage.

module mult_gate_sva (
  input  A,B,C,D,E,F,G,H,I,J,
  input  Y
);
  // Local recomputation of terms
  wire t1 = C & B & A;
  wire t2 = F & E & D;
  wire t3 = I & H & G;
  wire [3:0] terms = {t3,t2,t1,J};

  // Functional equivalence when inputs are known; also ensures Y is 0/1
  ap_func_no_x: assert property (@(*)
    (!$isunknown({A,B,C,D,E,F,G,H,I,J})) |->
      (!$isunknown(Y) && (Y == (|terms)))
  );

  // Simple dominance implications
  ap_dom_j:  assert property (@(*) J  |-> Y);
  ap_dom_t1: assert property (@(*) t1 |-> Y);
  ap_dom_t2: assert property (@(*) t2 |-> Y);
  ap_dom_t3: assert property (@(*) t3 |-> Y);

  // Zero-case implication
  ap_zero: assert property (@(*) (terms == 4'b0000) |-> (Y==1'b0));

  // Coverage: all key combinations and Y edges
  cv_none:   cover property (@(*) (terms == 4'b0000) && (Y==0)); // none true
  cv_j:      cover property (@(*) (terms == 4'b0001) && (Y==1)); // only J
  cv_t1:     cover property (@(*) (terms == 4'b0010) && (Y==1)); // only C&B&A
  cv_t2:     cover property (@(*) (terms == 4'b0100) && (Y==1)); // only F&E&D
  cv_t3:     cover property (@(*) (terms == 4'b1000) && (Y==1)); // only I&H&G

  cv_two:    cover property (@(*) ($countones(terms)==2) && (Y==1));
  cv_three:  cover property (@(*) ($countones(terms)==3) && (Y==1));
  cv_four:   cover property (@(*) ($countones(terms)==4) && (Y==1));

  cv_rise:   cover property (@(posedge Y) 1);
  cv_fall:   cover property (@(negedge Y) 1);
endmodule

bind mult_gate mult_gate_sva sva_i (.*);