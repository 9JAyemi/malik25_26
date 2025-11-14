// SVA for Synchro and Sincronizador
// Focus: 1-cycle latency, no combinational feedthrough, change-cause, knownness, and edge coverage

// Generic SVA for a single-bit 1-flop synchronizer
module Synchro_sva(input logic clk, dato, ds);

  // 1-cycle latency (guarded for first cycle/unknowns)
  property p_1cycle_delay;
    @(posedge clk) !$isunknown($past(dato)) |-> (ds == $past(dato));
  endproperty
  a_1cycle_delay: assert property (p_1cycle_delay);

  // Output becomes known if prior input sample was known
  property p_knownness;
    @(posedge clk) !$isunknown($past(dato)) |-> !$isunknown(ds);
  endproperty
  a_knownness: assert property (p_knownness);

  // Output changes only on clock edges (no glitches)
  a_change_only_on_clk: assert property ( $changed(ds) |-> $rose(clk) );

  // Any output change must be caused by an input change one cycle earlier
  property p_change_has_cause;
    @(posedge clk)
      (!$isunknown($past(dato,2)) && !$isunknown($past(dato)))
      |-> ( $changed(ds) |-> ($past(dato) != $past(dato,2)) );
  endproperty
  a_change_has_cause: assert property (p_change_has_cause);

  // Coverage: rising and falling edges propagate in exactly one cycle
  c_rise: cover property (@(posedge clk) $rose(dato) ##1 $rose(ds));
  c_fall: cover property (@(posedge clk) $fell(dato) ##1 $fell(ds));

endmodule

bind Synchro Synchro_sva u_synchro_sva(.clk(clk), .dato(dato), .ds(ds));


// Top-level SVA to also verify correct wiring of each channel
module Sincronizador_sva(
  input logic clk,
  input logic incambiarfuncion, incambiarsalida, inrst, inbtup, inbtdown,
  input logic outcambiarfuncion, outcambiarsalida, outrst, outbtup, outbtdown
);

  // Per-channel 1-cycle mapping (guarded)
  a_map_func: assert property (@(posedge clk)
    !$isunknown($past(incambiarfuncion)) |-> (outcambiarfuncion == $past(incambiarfuncion)));

  a_map_salida: assert property (@(posedge clk)
    !$isunknown($past(incambiarsalida)) |-> (outcambiarsalida == $past(incambiarsalida)));

  a_map_rst: assert property (@(posedge clk)
    !$isunknown($past(inrst)) |-> (outrst == $past(inrst)));

  a_map_up: assert property (@(posedge clk)
    !$isunknown($past(inbtup)) |-> (outbtup == $past(inbtup)));

  a_map_down: assert property (@(posedge clk)
    !$isunknown($past(inbtdown)) |-> (outbtdown == $past(inbtdown)));

  // All outputs only change on clock edges
  a_any_out_change_only_on_clk:
    assert property ( $changed({outcambiarfuncion,outcambiarsalida,outrst,outbtup,outbtdown}) |-> $rose(clk) );

  // Coverage: each channel propagates rising and falling edges in one cycle
  c_func_r:  cover property (@(posedge clk) $rose(incambiarfuncion) ##1 $rose(outcambiarfuncion));
  c_func_f:  cover property (@(posedge clk) $fell(incambiarfuncion) ##1 $fell(outcambiarfuncion));

  c_sal_r:   cover property (@(posedge clk) $rose(incambiarsalida) ##1 $rose(outcambiarsalida));
  c_sal_f:   cover property (@(posedge clk) $fell(incambiarsalida) ##1 $fell(outcambiarsalida));

  c_rst_r:   cover property (@(posedge clk) $rose(inrst) ##1 $rose(outrst));
  c_rst_f:   cover property (@(posedge clk) $fell(inrst) ##1 $fell(outrst));

  c_up_r:    cover property (@(posedge clk) $rose(inbtup) ##1 $rose(outbtup));
  c_up_f:    cover property (@(posedge clk) $fell(inbtup) ##1 $fell(outbtup));

  c_down_r:  cover property (@(posedge clk) $rose(inbtdown) ##1 $rose(outbtdown));
  c_down_f:  cover property (@(posedge clk) $fell(inbtdown) ##1 $fell(outbtdown));

endmodule

bind Sincronizador Sincronizador_sva u_sinc_sva(
  .clk(clk),
  .incambiarfuncion(incambiarfuncion),
  .incambiarsalida(incambiarsalida),
  .inrst(inrst),
  .inbtup(inbtup),
  .inbtdown(inbtdown),
  .outcambiarfuncion(outcambiarfuncion),
  .outcambiarsalida(outcambiarsalida),
  .outrst(outrst),
  .outbtup(outbtup),
  .outbtdown(outbtdown)
);