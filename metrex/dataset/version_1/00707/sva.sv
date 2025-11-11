// SVA checker for mux_2_1_en
module mux_2_1_en_sva (input logic in0, in1, en, out);

  // Functional equivalence (handles X-propagation)
  always_comb
    assert (out === (en ? in1 : in0))
      else $error("mux_2_1_en: out != (en ? in1 : in0)");

  // Selection edges reflect immediately
  assert property (@(posedge en)  ##0 (out === in1));
  assert property (@(negedge en)  ##0 (out === in0));

  // Data changes propagate when selected
  assert property (@(posedge in0) (en === 1'b0) |-> ##0 (out === 1'b1));
  assert property (@(negedge in0) (en === 1'b0) |-> ##0 (out === 1'b0));
  assert property (@(posedge in1) (en === 1'b1) |-> ##0 (out === 1'b1));
  assert property (@(negedge in1) (en === 1'b1) |-> ##0 (out === 1'b0));

  // Known select + selected input => known output
  assert property (@(in0 or in1 or en)
                   (!$isunknown(en) && ((en==0 && !$isunknown(in0)) || (en==1 && !$isunknown(in1))))
                   |-> ##0 !$isunknown(out));

  // Coverage
  cover property (@(posedge en)  ##0 (out === in1));
  cover property (@(negedge en)  ##0 (out === in0));
  cover property (@(posedge in0) (en==0) ##0 (out==1));
  cover property (@(negedge in0) (en==0) ##0 (out==0));
  cover property (@(posedge in1) (en==1) ##0 (out==1));
  cover property (@(negedge in1) (en==1) ##0 (out==0));
  cover property (@(in0 or in1 or en) (en==0 && out===in0 && !$isunknown({en,in0})));
  cover property (@(in0 or in1 or en) (en==1 && out===in1 && !$isunknown({en,in1})));
  cover property (@(in0 or in1 or en) ($isunknown(en) && (in0===in1) && (out===in0)));
  cover property (@(in0 or in1 or en) ($isunknown(en) && (in0!==in1) && $isunknown(out)));

endmodule

bind mux_2_1_en mux_2_1_en_sva (.in0(in0), .in1(in1), .en(en), .out(out));