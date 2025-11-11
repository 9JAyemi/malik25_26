// SVA for my_module
// Concise checks: functional correctness, mirror, independence of unused pins, and basic coverage.

module my_module_sva (
  input logic A1, A2, B1, B2, C1,
  input logic VPWR, VGND,
  input logic X, Y
);

  function logic rail_ok;
    return (VPWR === 1'b1 && VGND === 1'b0);
  endfunction

  // Functional NOR and buffer (when inputs are known and rails OK)
  property p_func_nor_buf;
    @(A1 or A2 or X or Y or VPWR or VGND)
      disable iff (!rail_ok())
      (!$isunknown({A1, A2})) |-> (X === ~(A1 | A2) && Y === X);
  endproperty
  assert property (p_func_nor_buf);

  // Y must always mirror X (rails OK)
  assert property (@(X or Y or VPWR or VGND)
    disable iff (!rail_ok())
    (Y === X));

  // Outputs must not depend on unused inputs B1/B2/C1 (rails OK)
  assert property (@(B1 or B2 or C1 or X or Y or VPWR or VGND)
    disable iff (!rail_ok())
    $changed({B1, B2, C1}) |-> ##0 $stable({X, Y}));

  // If A1/A2 are 0/1, outputs must be 0/1 (no X/Z) (rails OK)
  assert property (@(A1 or A2 or X or Y or VPWR or VGND)
    disable iff (!rail_ok())
    (!$isunknown({A1, A2})) |-> (!$isunknown({X, Y})));

  // Coverage: all input combinations of A1/A2 observed with correct outputs (rails OK)
  cover property (@(A1 or A2)
    rail_ok() && (A1==0 && A2==0) && (X==1 && Y==1));
  cover property (@(A1 or A2)
    rail_ok() && (A1==0 && A2==1) && (X==0 && Y==0));
  cover property (@(A1 or A2)
    rail_ok() && (A1==1 && A2==0) && (X==0 && Y==0));
  cover property (@(A1 or A2)
    rail_ok() && (A1==1 && A2==1) && (X==0 && Y==0));

  // Coverage: toggling unused inputs while outputs remain stable (rails OK)
  cover property (@(B1 or B2 or C1)
    rail_ok() && $changed({B1, B2, C1}) && $stable({A1, A2}) && $stable({X, Y}));

endmodule

// Bind into DUT
bind my_module my_module_sva u_my_module_sva (
  .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1),
  .VPWR(VPWR), .VGND(VGND), .X(X), .Y(Y)
);