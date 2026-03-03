// SVA for nor_and_gate
module nor_and_gate_sva (
  input logic A, B, C, D,
  input logic Y,
  input logic nor_out, and_out
);
  // White-box functional checks
  property p_nor;
    @(A or B or nor_out)
    disable iff ($isunknown({A,B,nor_out}))
    nor_out == ~(A | B);
  endproperty
  assert property (p_nor);

  property p_and;
    @(nor_out or C or D or and_out)
    disable iff ($isunknown({nor_out,C,D,and_out}))
    and_out == (nor_out & C & D);
  endproperty
  assert property (p_and);

  property p_buf;
    @(and_out or Y)
    disable iff ($isunknown({and_out,Y}))
    Y == and_out;
  endproperty
  assert property (p_buf);

  // End-to-end functional equivalence
  property p_e2e;
    @(A or B or C or D or Y)
    disable iff ($isunknown({A,B,C,D,Y}))
    Y == ((~(A | B)) & C & D);
  endproperty
  assert property (p_e2e);

  // Causality (no spurious transitions)
  property y_only_if_and_out_changes;
    @(and_out or Y)
    disable iff ($isunknown({and_out,Y}))
    $changed(Y) |-> $changed(and_out);
  endproperty
  assert property (y_only_if_and_out_changes);

  property and_only_if_inputs_change;
    @(nor_out or C or D or and_out)
    disable iff ($isunknown({nor_out,C,D,and_out}))
    $changed(and_out) |-> ($changed(nor_out) or $changed(C) or $changed(D));
  endproperty
  assert property (and_only_if_inputs_change);

  property nor_only_if_inputs_change;
    @(A or B or nor_out)
    disable iff ($isunknown({A,B,nor_out}))
    $changed(nor_out) |-> ($changed(A) or $changed(B));
  endproperty
  assert property (nor_only_if_inputs_change);

  // Output known when inputs known
  property y_known_when_inputs_known;
    @(A or B or C or D or Y)
    !$isunknown({A,B,C,D}) |-> !$isunknown(Y);
  endproperty
  assert property (y_known_when_inputs_known);

  // Coverage
  // Truth-table input coverage (all 16 input combinations)
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : tt_cov
      cover property (@(A or B or C or D)
        !$isunknown({A,B,C,D}) && {A,B,C,D} == i[3:0]);
    end
  endgenerate

  // Outcome and transition coverage
  cover property (@(A or B or C or D or Y) Y);
  cover property (@(A or B or C or D or Y) !Y);
  cover property (@(A or B or C or D or Y) $rose(Y));
  cover property (@(A or B or C or D or Y) $fell(Y));

  // Key functional corners
  cover property (@(A or B or C or D or Y) (!A && !B && C && D && Y));
  cover property (@(A or B or C or D or Y) ((A || B) && C && D && !Y));
  cover property (@(A or B or C or D or Y) (!C && !Y));
  cover property (@(A or B or C or D or Y) (!D && !Y));
endmodule

// Bind into DUT (white-box: taps internal nets)
bind nor_and_gate nor_and_gate_sva u_nor_and_gate_sva(
  .A(A), .B(B), .C(C), .D(D),
  .Y(Y),
  .nor_out(nor_out),
  .and_out(and_out)
);