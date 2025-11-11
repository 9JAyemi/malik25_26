// SVA for mux4to1. Bind this and provide clk/rst_n from your TB.
module mux4to1_sva(input logic clk, input logic rst_n);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Basic decode/inversion correctness
  a_inv_s0: assert property (~S0 === notS0);
  a_inv_s1: assert property (~S1 === notS1);

  // One-hot decoding of select minterms when selects are known
  a_onehot_dec: assert property (
    !$isunknown({S0,S1}) |-> $onehot({notS0andnotS1, S0andnotS1, notS0andS1, S0andS1})
  );

  // Output must be known when all inputs are known
  a_known_out: assert property (
    !$isunknown({S0,S1,D0,D1,D2,D3}) |-> !$isunknown(Y)
  );

  // Functional correctness (selected data drives Y)
  a_func: assert property (
    Y === (S1 ? (S0 ? D3 : D2) : (S0 ? D1 : D0))
  );

  // Propagation when selected: selected Di change causes Y change
  a_sel_prop0: assert property (({S1,S0}==2'b00 && !$isunknown(D0) && $changed(D0)) |-> $changed(Y));
  a_sel_prop1: assert property (({S1,S0}==2'b01 && !$isunknown(D1) && $changed(D1)) |-> $changed(Y));
  a_sel_prop2: assert property (({S1,S0}==2'b10 && !$isunknown(D2) && $changed(D2)) |-> $changed(Y));
  a_sel_prop3: assert property (({S1,S0}==2'b11 && !$isunknown(D3) && $changed(D3)) |-> $changed(Y));

  // Isolation when not selected: unselected Di changes do not affect Y
  a_iso0: assert property (($changed(D0) && ({S1,S0}!=2'b00)) |-> !$changed(Y));
  a_iso1: assert property (($changed(D1) && ({S1,S0}!=2'b01)) |-> !$changed(Y));
  a_iso2: assert property (($changed(D2) && ({S1,S0}!=2'b10)) |-> !$changed(Y));
  a_iso3: assert property (($changed(D3) && ({S1,S0}!=2'b11)) |-> !$changed(Y));

  // Coverage: exercise all select combos
  c_sel00: cover property ({S1,S0}==2'b00);
  c_sel01: cover property ({S1,S0}==2'b01);
  c_sel10: cover property ({S1,S0}==2'b10);
  c_sel11: cover property ({S1,S0}==2'b11);

  // Coverage: observe propagation from each selected input to Y
  c_prop0: cover property (({S1,S0}==2'b00 && !$isunknown(D0) && $changed(D0)) ##1 $changed(Y));
  c_prop1: cover property (({S1,S0}==2'b01 && !$isunknown(D1) && $changed(D1)) ##1 $changed(Y));
  c_prop2: cover property (({S1,S0}==2'b10 && !$isunknown(D2) && $changed(D2)) ##1 $changed(Y));
  c_prop3: cover property (({S1,S0}==2'b11 && !$isunknown(D3) && $changed(D3)) ##1 $changed(Y));
endmodule

bind mux4to1 mux4to1_sva u_mux4to1_sva(.clk(clk), .rst_n(rst_n));