// Bindable SVA checker for shift_register
module shift_register_sva;
  // Access DUT signals in bound scope
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;

  default disable iff (!past_valid);

  // Structural equivalence
  assert property (Q === Q2);

  // Q1 update rules
  assert property (LD  |=> (Q1 == $past(D)));
  assert property (!LD |=> (Q1 == $past(Q2)));

  // Q2 shift behavior
  assert property (SH  |=> (Q2 == { $past(Q1[14:0]), 1'b0 }));
  assert property (!SH |=> (Q2 == { 1'b0, $past(Q1[15:1]) }));

  // Boundary/inserted-zero checks
  assert property (SH  |=> (Q2[0]  == 1'b0 && Q2[15] == $past(Q1[14])));
  assert property (!SH |=> (Q2[15] == 1'b0 && Q2[0]  == $past(Q1[1])));

  // Output consistency (redundant but strong)
  assert property (SH  |-> (Q == { $past(Q1[14:0]), 1'b0 }));
  assert property (!SH |-> (Q == { 1'b0, $past(Q1[15:1]) }));

  // Functional coverage
  cover property (LD);
  cover property (SH);
  cover property (!SH);
  cover property (LD ##1 SH);
  cover property (LD ##1 !SH);
  cover property (SH ##1 !SH);
  cover property (!SH ##1 SH);
  cover property (LD && SH); // simultaneous LD and shift-left
endmodule

// Bind to DUT
bind shift_register shift_register_sva u_shift_register_sva();