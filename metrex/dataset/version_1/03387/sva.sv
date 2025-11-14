// SVA for Registro_Universal
// Concise checks for reset, hold/load behavior, next-state muxing, and basic coverage.

module Registro_Universal_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Asynchronous reset behavior
  ap_reset_async: assert property (@(posedge reset)
                                   (aumentar_actual==0 && disminuir_actual==0 &&
                                    out_aumentar==0 && out_disminuir==0));
  ap_reset_hold:  assert property (@(posedge clk) reset |-> 
                                   (aumentar_actual==0 && disminuir_actual==0 &&
                                    out_aumentar==0 && out_disminuir==0));

  // Outputs mirror registered state
  ap_out_matches_regs: assert property (out_aumentar==aumentar_actual &&
                                        out_disminuir==disminuir_actual);

  // Next-state mux correctness (combinational)
  always @* begin
    assert (chip_select
              ? (aumentar_next==aumentar && disminuir_next==disminuir)
              : (aumentar_next==aumentar_actual && disminuir_next==disminuir_actual))
      else $error("next-state mux mismatch");
  end

  // Hold when chip_select==0, load when chip_select==1
  ap_hold_cs0:  assert property (chip_select==0 |=> $stable(out_aumentar) && $stable(out_disminuir));
  ap_load_cs1_a: assert property (chip_select==1 |=> out_aumentar == $past(aumentar));
  ap_load_cs1_d: assert property (chip_select==1 |=> out_disminuir == $past(disminuir));

  // Clean (no X/Z) on key outputs/regs once out of reset
  ap_no_x: assert property (!$isunknown({out_aumentar,out_disminuir,aumentar_actual,disminuir_actual}));

  // Optional: chip_select well-defined when used
  ap_cs_defined: assert property (!$isunknown(chip_select));

  // Functional coverage
  cp_reset:      cover property (@(posedge reset) 1);
  cp_hold_path:  cover property (chip_select==0 ##1 $stable(out_aumentar) && $stable(out_disminuir));
  cp_load_path:  cover property (chip_select==1 ##1 (out_aumentar==$past(aumentar) && out_disminuir==$past(disminuir)));
  cp_toggle_a:   cover property (chip_select==1 ##1 $changed(out_aumentar));
  cp_toggle_d:   cover property (chip_select==1 ##1 $changed(out_disminuir));
endmodule

bind Registro_Universal Registro_Universal_sva sva_i();