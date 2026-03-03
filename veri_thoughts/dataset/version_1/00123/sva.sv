// SVA for mux_4_to_1. Bind into the DUT; focuses on correctness, X-safety, and path coverage.
module mux_4_to_1_sva(input logic D0, D1, D2, D3,
                      input logic S0, S1,
                      input logic Y);
  default clocking cb @(*); endclocking

  // Sanity: selects must be known (prevents latch-like behavior on X/Z)
  ap_sel_known: assert property (!$isunknown({S1,S0}));

  // Functional correctness: Y equals selected D
  ap_mux_00: assert property (({S1,S0}==2'b00) |-> (Y === D0));
  ap_mux_01: assert property (({S1,S0}==2'b01) |-> (Y === D1));
  ap_mux_10: assert property (({S1,S0}==2'b10) |-> (Y === D2));
  ap_mux_11: assert property (({S1,S0}==2'b11) |-> (Y === D3));

  // Causality: Y changes only due to select change or the selected D changing
  ap_change_cause: assert property (
    $changed(Y) |-> (
      $changed({S1,S0}) ||
      (({S1,S0}==2'b00) && $changed(D0)) ||
      (({S1,S0}==2'b01) && $changed(D1)) ||
      (({S1,S0}==2'b10) && $changed(D2)) ||
      (({S1,S0}==2'b11) && $changed(D3))
    )
  );

  // Coverage: hit all select values
  cp_sel_00: cover property ({S1,S0}==2'b00);
  cp_sel_01: cover property ({S1,S0}==2'b01);
  cp_sel_10: cover property ({S1,S0}==2'b10);
  cp_sel_11: cover property ({S1,S0}==2'b11);

  // Coverage: each data path propagates both rising and falling edges to Y while select is stable
  cp_path00_rise: cover property ($stable({S1,S0}) && ({S1,S0}==2'b00) && $rose(D0) && $rose(Y));
  cp_path00_fall: cover property ($stable({S1,S0}) && ({S1,S0}==2'b00) && $fell(D0) && $fell(Y));
  cp_path01_rise: cover property ($stable({S1,S0}) && ({S1,S0}==2'b01) && $rose(D1) && $rose(Y));
  cp_path01_fall: cover property ($stable({S1,S0}) && ({S1,S0}==2'b01) && $fell(D1) && $fell(Y));
  cp_path10_rise: cover property ($stable({S1,S0}) && ({S1,S0}==2'b10) && $rose(D2) && $rose(Y));
  cp_path10_fall: cover property ($stable({S1,S0}) && ({S1,S0}==2'b10) && $fell(D2) && $fell(Y));
  cp_path11_rise: cover property ($stable({S1,S0}) && ({S1,S0}==2'b11) && $rose(D3) && $rose(Y));
  cp_path11_fall: cover property ($stable({S1,S0}) && ({S1,S0}==2'b11) && $fell(D3) && $fell(Y));
endmodule

bind mux_4_to_1 mux_4_to_1_sva sva_mux_4_to_1(.*);