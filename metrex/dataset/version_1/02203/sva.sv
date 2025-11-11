// SVA for mux4to1. Bind this to the DUT.
// Concise, high-quality checks with essential coverage.

module mux4to1_sva (
  input logic [1:0] S,
  input logic D0, D1, D2, D3,
  input logic OE,
  input logic Y
);

  // Combinational sampling on any input/control change
  default clocking cb @ (S or D0 or D1 or D2 or D3 or OE); endclocking

  // Golden functional equivalence with 4-state semantics (matches DUT ternary behavior)
  a_func_equiv: assert property (
    Y === (OE ? ((S==2'b00) ? D0 :
                 (S==2'b01) ? D1 :
                 (S==2'b10) ? D2 :
                 (S==2'b11) ? D3 : 1'b0) : 1'b0)
  );

  // OE low must force output low (redundant with a_func_equiv but clearer failure)
  a_oe_low_forces_zero: assert property (!OE |-> ##0 (Y==1'b0));

  // Selected data must immediately drive Y (sanity of each path)
  a_sel00_path: assert property (OE && (S==2'b00) && $changed(D0) |-> ##0 $changed(Y));
  a_sel01_path: assert property (OE && (S==2'b01) && $changed(D1) |-> ##0 $changed(Y));
  a_sel10_path: assert property (OE && (S==2'b10) && $changed(D2) |-> ##0 $changed(Y));
  a_sel11_path: assert property (OE && (S==2'b11) && $changed(D3) |-> ##0 $changed(Y));

  // Minimal but meaningful coverage
  c_oe0_seen:   cover property (!OE);
  c_sel00_seen: cover property (OE && (S==2'b00));
  c_sel01_seen: cover property (OE && (S==2'b01));
  c_sel10_seen: cover property (OE && (S==2'b10));
  c_sel11_seen: cover property (OE && (S==2'b11));

  // Show data->Y propagation for each select
  c_d0_to_y: cover property (OE && (S==2'b00) && $changed(D0) ##0 $changed(Y));
  c_d1_to_y: cover property (OE && (S==2'b01) && $changed(D1) ##0 $changed(Y));
  c_d2_to_y: cover property (OE && (S==2'b10) && $changed(D2) ##0 $changed(Y));
  c_d3_to_y: cover property (OE && (S==2'b11) && $changed(D3) ##0 $changed(Y));

  // Output value coverage
  c_y0: cover property (Y==1'b0);
  c_y1: cover property (Y==1'b1);

endmodule

// Bind into the DUT
bind mux4to1 mux4to1_sva mux4to1_sva_i (
  .S(S), .D0(D0), .D1(D1), .D2(D2), .D3(D3), .OE(OE), .Y(Y)
);