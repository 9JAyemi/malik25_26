// SVA for mux: concise, full functional checks + coverage
module mux_sva (
  input logic [3:0] D,
  input logic       EN,
  input logic [1:0] SEL,
  input logic       Y
);

  // Trigger assertions on any relevant combinational change
  event comb_ev;
  always @(D or EN or SEL or Y) -> comb_ev;

  // Helper: selected data bit
  function automatic logic sel_bit (logic [3:0] d, logic [1:0] s);
    case (s)
      2'b00: sel_bit = d[0];
      2'b01: sel_bit = d[1];
      2'b10: sel_bit = d[2];
      default: sel_bit = d[3];
    endcase
  endfunction

  // Spec holds when inputs are known
  property p_spec_when_known;
    @(comb_ev) !$isunknown({EN,SEL,D}) |-> (Y == (EN ? sel_bit(D,SEL) : 1'b0));
  endproperty
  assert property (p_spec_when_known);

  // EN low forces Y=0 regardless of D/SEL unknowns
  property p_en_forces_zero;
    @(comb_ev) (EN === 1'b0) |-> (Y === 1'b0);
  endproperty
  assert property (p_en_forces_zero);

  // No spurious Y change if inputs are stable
  property p_no_spurious_y_change;
    @(comb_ev) $stable({EN,SEL,D}) |-> $stable(Y);
  endproperty
  assert property (p_no_spurious_y_change);

  // Functional coverage: each select path and EN=0 behavior
  cover property (@(comb_ev) EN && SEL==2'b00 && Y==D[0]);
  cover property (@(comb_ev) EN && SEL==2'b01 && Y==D[1]);
  cover property (@(comb_ev) EN && SEL==2'b10 && Y==D[2]);
  cover property (@(comb_ev) EN && SEL==2'b11 && Y==D[3]);
  cover property (@(comb_ev) !EN && Y==1'b0);

endmodule

// Bind to DUT
bind mux mux_sva mux_sva_i (.D(D), .EN(EN), .SEL(SEL), .Y(Y));