// SVA for digit_select. Bind this to the DUT instance.
module digit_select_sva(
  input logic [3:0] d1,
  input logic [3:0] d2,
  input logic [3:0] d3,
  input logic [3:0] d4,
  input logic [1:0] control,
  input logic [3:0] digit
);

  // Disallow X/Z on control (combinational block avoids race with continuous assigns)
  always_comb
    assert (!$isunknown(control))
      else $error("digit_select: control has X/Z");

  // Functional correctness (four-state exact match), sampled after ##0 to avoid races
  property sel11; @(control or d1 or d2 or d3 or d4) (control===2'b11) |-> ##0 (digit===d1); endproperty
  property sel10; @(control or d1 or d2 or d3 or d4) (control===2'b10) |-> ##0 (digit===d2); endproperty
  property sel01; @(control or d1 or d2 or d3 or d4) (control===2'b01) |-> ##0 (digit===d3); endproperty
  property sel00; @(control or d1 or d2 or d3 or d4) (control===2'b00) |-> ##0 (digit===d4); endproperty

  assert property (sel11);
  assert property (sel10);
  assert property (sel01);
  assert property (sel00);

  // Non-interference: changes on non-selected inputs alone must not affect digit
  property ni11;
    @(control or d1 or d2 or d3 or d4)
      (control===2'b11 && !$changed(control) && !$changed(d1) &&
       ($changed(d2) || $changed(d3) || $changed(d4))) |-> ##0 $stable(digit);
  endproperty
  property ni10;
    @(control or d1 or d2 or d3 or d4)
      (control===2'b10 && !$changed(control) && !$changed(d2) &&
       ($changed(d1) || $changed(d3) || $changed(d4))) |-> ##0 $stable(digit);
  endproperty
  property ni01;
    @(control or d1 or d2 or d3 or d4)
      (control===2'b01 && !$changed(control) && !$changed(d3) &&
       ($changed(d1) || $changed(d2) || $changed(d4))) |-> ##0 $stable(digit);
  endproperty
  property ni00;
    @(control or d1 or d2 or d3 or d4)
      (control===2'b00 && !$changed(control) && !$changed(d4) &&
       ($changed(d1) || $changed(d2) || $changed(d3))) |-> ##0 $stable(digit);
  endproperty

  assert property (ni11);
  assert property (ni10);
  assert property (ni01);
  assert property (ni00);

  // Coverage: hit each select path
  cover property (@(control or d1 or d2 or d3 or d4) (control===2'b00) ##0 (digit===d4));
  cover property (@(control or d1 or d2 or d3 or d4) (control===2'b01) ##0 (digit===d3));
  cover property (@(control or d1 or d2 or d3 or d4) (control===2'b10) ##0 (digit===d2));
  cover property (@(control or d1 or d2 or d3 or d4) (control===2'b11) ##0 (digit===d1));

  // Coverage: observe non-interference scenarios
  cover property (@(control or d1 or d2 or d3 or d4) control===2'b11 && !$changed(control) && !$changed(d1) &&
                                           ($changed(d2) || $changed(d3) || $changed(d4)));
  cover property (@(control or d1 or d2 or d3 or d4) control===2'b10 && !$changed(control) && !$changed(d2) &&
                                           ($changed(d1) || $changed(d3) || $changed(d4)));
  cover property (@(control or d1 or d2 or d3 or d4) control===2'b01 && !$changed(control) && !$changed(d3) &&
                                           ($changed(d1) || $changed(d2) || $changed(d4)));
  cover property (@(control or d1 or d2 or d3 or d4) control===2'b00 && !$changed(control) && !$changed(d4) &&
                                           ($changed(d1) || $changed(d2) || $changed(d3)));

endmodule

bind digit_select digit_select_sva sva_digit_select (.*);