// SVA for sky130_fd_sc_ls__a21oi
// Function derived: Y = (~A1) | (A2 & ~B1)

module sky130_fd_sc_ls__a21oi_sva (input logic A1, A2, B1, Y);
  // Fire on any input change; sample one delta later to avoid race with combinational settle
  event ev;
  always @(A1 or A2 or B1) -> ev;

  // 4-state functional equivalence (matches gate-level X/Z propagation)
  property p_func_4state;
    @(ev) ##0 (Y === ((~A1 & ~A2) | (~A1 & B1) | (A2 & ~B1)));
  endproperty
  assert property (p_func_4state);

  // Known-input functional check using simplified form (2-state equality)
  property p_func_known_inputs;
    @(ev) (!$isunknown({A1,A2,B1})) |-> ##0 (Y == ((~A1) | (A2 & ~B1)));
  endproperty
  assert property (p_func_known_inputs);

  // If inputs are known, output must be known
  property p_known_out_when_known_in;
    @(ev) (!$isunknown({A1,A2,B1})) |-> ##0 !$isunknown(Y);
  endproperty
  assert property (p_known_out_when_known_in);

  // Key implications (robust even with Xs on unrelated inputs)
  assert property (@(ev) (A1 === 1'b0)         |-> ##0 (Y === 1'b1));
  assert property (@(ev) (A1 === 1'b1 && B1===1'b1) |-> ##0 (Y === 1'b0));
  assert property (@(ev) (A1 === 1'b1 && A2===1'b0) |-> ##0 (Y === 1'b0));
  assert property (@(ev) (A1 === 1'b1 && A2===1'b1 && B1===1'b0) |-> ##0 (Y === 1'b1));

  // Full input-state coverage with expected Y
  cover property (@(ev) ##0 (A1==0 && A2==0 && B1==0 && Y==1));
  cover property (@(ev) ##0 (A1==0 && A2==0 && B1==1 && Y==1));
  cover property (@(ev) ##0 (A1==0 && A2==1 && B1==0 && Y==1));
  cover property (@(ev) ##0 (A1==0 && A2==1 && B1==1 && Y==1));
  cover property (@(ev) ##0 (A1==1 && A2==0 && B1==0 && Y==0));
  cover property (@(ev) ##0 (A1==1 && A2==0 && B1==1 && Y==0));
  cover property (@(ev) ##0 (A1==1 && A2==1 && B1==0 && Y==1));
  cover property (@(ev) ##0 (A1==1 && A2==1 && B1==1 && Y==0));

  // Output value coverage
  cover property (@(ev) ##0 (Y==1));
  cover property (@(ev) ##0 (Y==0));
endmodule

bind sky130_fd_sc_ls__a21oi sky130_fd_sc_ls__a21oi_sva u_a21oi_sva (.A1(A1), .A2(A2), .B1(B1), .Y(Y));