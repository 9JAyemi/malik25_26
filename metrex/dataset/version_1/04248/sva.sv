// SVA for module 'inicial'. Focused, concise, full transition/output checking and coverage.
// Bind this file alongside the DUT.

module inicial_sva (
  input logic        clock,
  input logic        botao, aberto, fechado, motor, sentido,
  input logic        ledVerde, ledVermelho,
  input logic [6:0]  display,
  input logic [1:0]  estado
);
  // Sample after the active region (post-update)
  default clocking cb @(posedge clock);
    input #1step botao, aberto, fechado, motor, sentido, ledVerde, ledVermelho, display, estado;
  endclocking

  localparam logic [1:0] S_Fechado  = 2'b00,
                         S_Abrindo  = 2'b01,
                         S_Aberto   = 2'b10,
                         S_Fechando = 2'b11;

  // Helpful lets
  let in5 = {botao,aberto,fechado,motor,sentido};

  let trig_Fechado_to_Abrindo  = (in5 == 5'b10110);
  let trig_Abrindo_to_Aberto   = (in5 == 5'b10010);
  let trig_Abrindo_to_Fechando = (in5 == 5'b00010);
  let trig_Aberto_to_Fechando  = (in5 == 5'b01011);
  let trig_Fechando_to_Abrindo = (in5 == 5'b10011);
  let trig_Fechando_to_Fechado = (in5 == 5'b00011);

  // Basic sanity
  assert property ( !$isunknown(estado) );
  assert property ( !(ledVerde && ledVermelho) ); // never both LEDs on
  assert property ( display inside {7'b0001110, 7'b1000000, 7'b0001000} );

  // Next-state transition checks (based on previous state and current inputs)
  assert property ( ($past(estado) == S_Fechado  &&  trig_Fechado_to_Abrindo)  |-> (estado == S_Abrindo) );
  assert property ( ($past(estado) == S_Abrindo  &&  trig_Abrindo_to_Aberto)   |-> (estado == S_Aberto) );
  assert property ( ($past(estado) == S_Abrindo  &&  trig_Abrindo_to_Fechando) |-> (estado == S_Fechando) );
  assert property ( ($past(estado) == S_Aberto   &&  trig_Aberto_to_Fechando)  |-> (estado == S_Fechando) );
  assert property ( ($past(estado) == S_Fechando &&  trig_Fechando_to_Abrindo) |-> (estado == S_Abrindo) );
  assert property ( ($past(estado) == S_Fechando &&  trig_Fechando_to_Fechado) |-> (estado == S_Fechado) );

  // Hold-state when no trigger
  assert property ( ($past(estado)==S_Fechado)  && !trig_Fechado_to_Abrindo  |-> (estado==S_Fechado) );
  assert property ( ($past(estado)==S_Abrindo)  && !(trig_Abrindo_to_Aberto || trig_Abrindo_to_Fechando) |-> (estado==S_Abrindo) );
  assert property ( ($past(estado)==S_Aberto)   && !trig_Aberto_to_Fechando  |-> (estado==S_Aberto) );
  assert property ( ($past(estado)==S_Fechando) && !(trig_Fechando_to_Abrindo || trig_Fechando_to_Fechado) |-> (estado==S_Fechando) );

  // No illegal jumps
  assert property ( ($past(estado)==S_Fechado)  |-> (estado inside {S_Fechado,S_Abrindo}) );
  assert property ( ($past(estado)==S_Abrindo)  |-> (estado inside {S_Abrindo,S_Aberto,S_Fechando}) );
  assert property ( ($past(estado)==S_Aberto)   |-> (estado inside {S_Aberto,S_Fechando}) );
  assert property ( ($past(estado)==S_Fechando) |-> (estado inside {S_Fechando,S_Fechado,S_Abrindo}) );

  // Output decoding: outputs follow previous cycle's state (as coded in the DUT)
  assert property ( ($past(estado)==S_Fechado)  |-> (display==7'b0001110 && !ledVerde && !ledVermelho) );
  assert property ( ($past(estado)==S_Abrindo)  |-> (display==7'b1000000 &&  ledVerde && !ledVermelho) );
  assert property ( ($past(estado)==S_Aberto)   |-> (display==7'b0001000 && !ledVerde && !ledVermelho) );
  assert property ( ($past(estado)==S_Fechando) |-> (display==7'b1000000 && !ledVerde &&  ledVermelho) );

  // Coverage: visit all states and all transitions
  cover property ( estado==S_Fechado );
  cover property ( estado==S_Abrindo );
  cover property ( estado==S_Aberto );
  cover property ( estado==S_Fechando );

  cover property ( ($past(estado)==S_Fechado)  &&  trig_Fechado_to_Abrindo  |-> (estado==S_Abrindo) );
  cover property ( ($past(estado)==S_Abrindo)  &&  trig_Abrindo_to_Aberto   |-> (estado==S_Aberto) );
  cover property ( ($past(estado)==S_Abrindo)  &&  trig_Abrindo_to_Fechando |-> (estado==S_Fechando) );
  cover property ( ($past(estado)==S_Aberto)   &&  trig_Aberto_to_Fechando  |-> (estado==S_Fechando) );
  cover property ( ($past(estado)==S_Fechando) &&  trig_Fechando_to_Abrindo |-> (estado==S_Abrindo) );
  cover property ( ($past(estado)==S_Fechando) &&  trig_Fechando_to_Fechado |-> (estado==S_Fechado) );

  // Coverage: observe each output pattern at least once
  cover property ( display==7'b0001110 && !ledVerde && !ledVermelho );
  cover property ( display==7'b0001000 && !ledVerde && !ledVermelho );
  cover property ( display==7'b1000000 &&  ledVerde && !ledVermelho );
  cover property ( display==7'b1000000 && !ledVerde &&  ledVermelho );

endmodule

bind inicial inicial_sva sv_inicial_sva (
  .clock      (clock),
  .botao      (botao),
  .aberto     (aberto),
  .fechado    (fechado),
  .motor      (motor),
  .sentido    (sentido),
  .ledVerde   (ledVerde),
  .ledVermelho(ledVermelho),
  .display    (display),
  .estado     (estado)
);