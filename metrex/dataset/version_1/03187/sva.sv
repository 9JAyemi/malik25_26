// SVA for module sub
// Bindable checker module (no TB/DUT edits required)
module sub_sva (input logic subsig1, subsig2, subout);

  // Functional equivalence (combinational, handles delta cycles)
  // If subsig2 is known 0/1, subout must be its complement and 2-state
  always_comb
    assert (#0) ($isunknown(subsig2) || (subout === ~subsig2))
      else $error("subout must equal ~subsig2 when subsig2 is known");

  // Any subout change must be caused by subsig2 change
  property p_out_change_caused_by_subsig2;
    @(posedge subout or negedge subout) $changed(subsig2);
  endproperty
  assert property (p_out_change_caused_by_subsig2)
    else $error("subout changed without subsig2 change");

  // On subsig2 edge, subout must immediately reflect complement
  property p_out_matches_not_on_subsig2_edge;
    @(posedge subsig2 or negedge subsig2) ##0 (subout === ~subsig2);
  endproperty
  assert property (p_out_matches_not_on_subsig2_edge)
    else $error("subout != ~subsig2 at subsig2 edge");

  // Independence: subsig1 must not affect subout when subsig2 is stable
  property p_independent_of_subsig1;
    @(posedge subsig1 or negedge subsig1) $stable(subsig2) |-> ##0 $stable(subout);
  endproperty
  assert property (p_independent_of_subsig1)
    else $error("subout depends on subsig1");

  // Coverage: all input combinations and resulting output
  cover property (@(posedge subsig1 or negedge subsig1 or posedge subsig2 or negedge subsig2)
                  (subsig1===0 && subsig2===0 && subout===1));
  cover property (@(posedge subsig1 or negedge subsig1 or posedge subsig2 or negedge subsig2)
                  (subsig1===1 && subsig2===0 && subout===1));
  cover property (@(posedge subsig1 or negedge subsig1 or posedge subsig2 or negedge subsig2)
                  (subsig1===0 && subsig2===1 && subout===0));
  cover property (@(posedge subsig1 or negedge subsig1 or posedge subsig2 or negedge subsig2)
                  (subsig1===1 && subsig2===1 && subout===0));

  // Coverage: correct polarity on subsig2 toggles
  cover property (@(posedge subsig2) (subout==0));
  cover property (@(negedge subsig2) (subout==1));

endmodule

bind sub sub_sva u_sub_sva (.subsig1(subsig1), .subsig2(subsig2), .subout(subout));