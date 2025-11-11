// SVA for my_module
module my_module_sva (
  input logic        Y,
  input logic        A,
  input logic [1:0]  B_N,
  input logic        VPWR
);

  // Sample on any input change; use ##0 to evaluate after combinational settle
  default clocking cb @(A or B_N or VPWR); endclocking

  // Power-off dominates output
  property p_poweroff_dominates;
    (VPWR === 1'b0) |-> ##0 (Y === 1'b0);
  endproperty
  assert property (p_poweroff_dominates);

  // Functional equivalence when inputs known and power on
  property p_equiv_when_known;
    (VPWR === 1'b1 && !$isunknown({A,B_N})) |-> ##0 (Y === ((~A) && (B_N == 2'b01)));
  endproperty
  assert property (p_equiv_when_known);

  // Output high only under exact condition
  property p_y_one_only_if;
    (Y === 1'b1) |-> ##0 (VPWR === 1'b1 && A === 1'b0 && B_N === 2'b01);
  endproperty
  assert property (p_y_one_only_if);

  // No X/Z on Y when inputs are known
  property p_no_x_on_y_when_inputs_known;
    (!$isunknown({VPWR,A,B_N})) |-> ##0 (!$isunknown(Y));
  endproperty
  assert property (p_no_x_on_y_when_inputs_known);

  // Coverage: power-off and all power-on input combinations
  cover property (VPWR === 1'b0 ##0 Y === 1'b0);

  cover property (VPWR === 1'b1 && A===1'b0 && B_N===2'b01 ##0 Y===1'b1);

  cover property (VPWR === 1'b1 && A===1'b0 && B_N===2'b00 ##0 Y===1'b0);
  cover property (VPWR === 1'b1 && A===1'b0 && B_N===2'b10 ##0 Y===1'b0);
  cover property (VPWR === 1'b1 && A===1'b0 && B_N===2'b11 ##0 Y===1'b0);
  cover property (VPWR === 1'b1 && A===1'b1 && B_N===2'b00 ##0 Y===1'b0);
  cover property (VPWR === 1'b1 && A===1'b1 && B_N===2'b01 ##0 Y===1'b0);
  cover property (VPWR === 1'b1 && A===1'b1 && B_N===2'b10 ##0 Y===1'b0);
  cover property (VPWR === 1'b1 && A===1'b1 && B_N===2'b11 ##0 Y===1'b0);

endmodule

bind my_module my_module_sva u_my_module_sva (.Y(Y), .A(A), .B_N(B_N), .VPWR(VPWR));