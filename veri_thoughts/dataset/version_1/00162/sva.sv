// SVA checker for mux4to1
module mux4to1_sva (
  input I0, I1, I2, I3, S,
  input not_S, sel1, sel2,
  input O
);

  // End-to-end functional equivalence
  assert property (@(I0 or I1 or I2 or I3 or S)
    O == ((S ? I1 : I0) ^ (S ? I3 : I2))
  );

  // Internal combinational correctness
  assert property (@(S) not_S == ~S);
  assert property (@(I0 or I1 or S) sel1 == ((~S & I0) | (S & I1)));
  assert property (@(I2 or I3 or S) sel2 == ((~S & I2) | (S & I3)));
  assert property (@(I0 or I1 or I2 or I3 or S) O == (sel1 ^ sel2));

  // X/Z propagation check
  assert property (@(I0 or I1 or I2 or I3 or S)
    !$isunknown({I0,I1,I2,I3,S}) |-> !$isunknown({not_S,sel1,sel2,O})
  );

  // Behavior on S edges: output changes iff contributing XORs differ
  assert property (@(posedge S or negedge S)
    !$isunknown({I0,I1,I2,I3,S,O}) && ((I0^I2)!=(I1^I3)) |-> O != $past(O)
  );
  assert property (@(posedge S or negedge S)
    !$isunknown({I0,I1,I2,I3,S,O}) && ((I0^I2)==(I1^I3)) |-> O == $past(O)
  );

  // sel1/sel2 toggle expectations on S edges
  assert property (@(posedge S or negedge S)
    !$isunknown({I0,I1,S,sel1}) && (I0^I1) |-> sel1 != $past(sel1)
  );
  assert property (@(posedge S or negedge S)
    !$isunknown({I0,I1,S,sel1}) && !(I0^I1) |-> sel1 == $past(sel1)
  );
  assert property (@(posedge S or negedge S)
    !$isunknown({I2,I3,S,sel2}) && (I2^I3) |-> sel2 != $past(sel2)
  );
  assert property (@(posedge S or negedge S)
    !$isunknown({I2,I3,S,sel2}) && !(I2^I3) |-> sel2 == $past(sel2)
  );

  // Minimal functional coverage
  cover property (@(I0 or I1 or I2 or I3 or S) S==0);
  cover property (@(I0 or I1 or I2 or I3 or S) S==1);
  cover property (@(I0 or I1 or I2 or I3 or S) O==0);
  cover property (@(I0 or I1 or I2 or I3 or S) O==1);
  cover property (@(posedge S) ((I0^I2)!=(I1^I3)) && (O != $past(O)));
  cover property (@(negedge S) ((I0^I2)!=(I1^I3)) && (O != $past(O)));

endmodule

// Bind into DUT
bind mux4to1 mux4to1_sva u_mux4to1_sva (
  .I0(I0), .I1(I1), .I2(I2), .I3(I3), .S(S),
  .not_S(not_S), .sel1(sel1), .sel2(sel2), .O(O)
);