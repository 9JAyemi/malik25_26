// SVA for conmutacion
module conmutacion_sva (
  input  logic        CLKOUTseg,
  input  logic [3:0]  centenas,
  input  logic [3:0]  decenas,
  input  logic [3:0]  unidades,
  input  logic        C,
  input  logic        De,
  input  logic        U,
  input  logic [1:0]  mostrar,
  input  logic [3:0]  digito,
  input  logic [1:0]  titileo
);
  default clocking cb @(posedge CLKOUTseg); endclocking

  bit past_valid;
  always_ff @(posedge CLKOUTseg) past_valid <= 1'b1;

  // Sanity/encoding
  assert property (disable iff (!past_valid) !$isunknown({titileo, mostrar, digito}));
  assert property (disable iff (!past_valid) mostrar inside {2'b01,2'b10,2'b11});

  // titileo update rules (use $past(...) to reference the cycle that drove the update)
  assert property (disable iff (!past_valid) (!$past(U)) |-> (titileo == 2'b00));
  assert property (disable iff (!past_valid) ($past(U && !De)) |-> (titileo == 2'b01));
  assert property (disable iff (!past_valid) ($past(U && De)) |-> (
      ($past(titileo)==2'b00 && titileo==2'b01) ||
      ($past(titileo)==2'b01 && titileo==2'b10) ||
      ($past(titileo)==2'b10 && titileo==2'b11) ||
      ($past(titileo)==2'b11 && titileo==2'b00)
  ));

  // Output mapping corresponds to previous titileo (due to NBA scheduling)
  assert property (disable iff (!past_valid) ($past(titileo)==2'b00) |-> (mostrar==2'b01 && digito==4'd0));
  assert property (disable iff (!past_valid) ($past(titileo)==2'b01) |-> (mostrar==2'b01 && digito==unidades));
  assert property (disable iff (!past_valid) ($past(titileo)==2'b10) |-> (mostrar==2'b10 && digito==decenas));
  assert property (disable iff (!past_valid) ($past(titileo)==2'b11) |-> (mostrar==2'b11 && digito==centenas));

  // Purely observable cross-checks (do not rely on internals)
  assert property (disable iff (!past_valid) (mostrar==2'b01) |-> (digito==4'd0 || digito==unidades));
  assert property (disable iff (!past_valid) (mostrar==2'b10) |-> (digito==decenas));
  assert property (disable iff (!past_valid) (mostrar==2'b11) |-> (digito==centenas));

  // Coverage: states, wrap, and control effects
  cover property (past_valid && titileo==2'b00);
  cover property (past_valid && titileo==2'b01);
  cover property (past_valid && titileo==2'b10);
  cover property (past_valid && titileo==2'b11);

  cover property (disable iff (!past_valid)
                  ($past(U && De) && $past(titileo)==2'b11 && titileo==2'b00));
  cover property (disable iff (!past_valid)
                  ($past(!U) && $past(titileo) inside {2'b01,2'b10,2'b11} && titileo==2'b00));
  cover property (disable iff (!past_valid)
                  ($past(U && !De) && titileo==2'b01));

  cover property (disable iff (!past_valid) (mostrar==2'b01 && digito==4'd0));
  cover property (disable iff (!past_valid) (mostrar==2'b01 && digito==unidades));
  cover property (disable iff (!past_valid) (mostrar==2'b10 && digito==decenas));
  cover property (disable iff (!past_valid) (mostrar==2'b11 && digito==centenas));
endmodule

// Bind into DUT (exposes internal titileo)
bind conmutacion conmutacion_sva conmutacion_sva_i (
  .CLKOUTseg(CLKOUTseg),
  .centenas(centenas),
  .decenas(decenas),
  .unidades(unidades),
  .C(C),
  .De(De),
  .U(U),
  .mostrar(mostrar),
  .digito(digito),
  .titileo(titileo)
)