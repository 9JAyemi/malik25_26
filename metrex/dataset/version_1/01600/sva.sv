// SVA for Divisor_Frecuencia
// Checks: counter increment/wrap, toggle correctness, period, bounds, no-X; plus key coverage.
module Divisor_Frecuencia_sva #(parameter int unsigned MAX = 50_000_000-1)
(
  input  logic        C_100Mhz,
  input  logic        C_1Hz,
  input  logic [31:0] contador
);
  default clocking cb @(posedge C_100Mhz); endclocking

  bit past_valid;
  always_ff @(posedge C_100Mhz) past_valid <= 1'b1;

  // Sanity
  assert property (contador <= MAX);
  assert property (!$isunknown({contador, C_1Hz}));

  // Correct step when not wrapping
  assert property (disable iff (!past_valid)
                   $past(contador) != MAX |-> (contador == $past(contador)+1 && !$changed(C_1Hz)));

  // Correct wrap and toggle
  assert property (disable iff (!past_valid)
                   $past(contador) == MAX |-> (contador == 0 && $changed(C_1Hz)));

  // Toggle occurs only on wrap
  assert property (disable iff (!past_valid)
                   $changed(C_1Hz) |-> $past(contador) == MAX);

  // Exact period: stable for MAX cycles between toggles, then toggle
  assert property (disable iff (!past_valid)
                   $changed(C_1Hz) |-> !$changed(C_1Hz)[*MAX] ##1 $changed(C_1Hz));

  // Coverage
  cover property ($rose(C_1Hz));
  cover property ($fell(C_1Hz));
  cover property (contador == MAX);
  cover property ($changed(C_1Hz) ##1 !$changed(C_1Hz)[*MAX] ##1 $changed(C_1Hz));
endmodule

bind Divisor_Frecuencia Divisor_Frecuencia_sva #(.MAX(50_000_000-1))
  i_divisor_freq_sva (.C_100Mhz(C_100Mhz), .C_1Hz(C_1Hz), .contador(contador));