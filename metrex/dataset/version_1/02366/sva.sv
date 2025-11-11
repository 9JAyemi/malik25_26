// SVA for VerificadorSentidoMovimiento
// Focus: single golden functional assertion with priority-accurate spec,
// X-safety on output, hold behavior on unsupported floors, and concise coverage.

module VerificadorSentidoMovimiento_sva
(
  input logic              _clk_,
  input logic              FSM_ready_in,
  input logic [2:0]        piso_actual,
  input logic [1:0]        solicitud_ps,
  input logic [1:0]        solicitud_p1,
  input logic [1:0]        solicitud_p2,
  input logic [1:0]        solicitud_p3,
  input logic [1:0]        solicitud_p4,
  input logic [1:0]        accion
);

  default clocking cb @(posedge _clk_); endclocking

  // Case-equality helper (matches the DUT’s masked intent, i.e., "x" as don't-care)
  function automatic bit eqx2 (logic [1:0] a, logic [1:0] pat);
    return (a === pat);
  endfunction

  // Priority-accurate next-state spec derived from the RTL order (last assignment wins)
  function automatic logic [1:0] exp_next
  (
    logic [2:0] piso,
    logic [1:0] s_ps, s_p1, s_p2, s_p3, s_p4,
    logic [1:0] prev
  );
    logic [1:0] r;
    r = prev; // default: hold

    unique case (piso)
      // piso 0 (000)
      3'b000: begin
        if (eqx2(s_p1,2'bx0) || eqx2(s_p2,2'bx0) || eqx2(s_p3,2'bx0) || eqx2(s_p4,2'bx0)) r = 2'b10;
        else if (eqx2(s_ps,2'bx0)) r = 2'b01;
        else if (eqx2(s_ps,2'bx1)) r = 2'b00;
      end

      // piso 1 (001)
      3'b001: begin
        if      (eqx2(s_ps,2'b0x))                                     r = 2'b10;
        else if (eqx2(s_p3,2'b1x) || eqx2(s_p4,2'b1x))                 r = 2'b10;
        else if (eqx2(s_p3,2'bx1) || eqx2(s_p4,2'bx1))                 r = 2'b11;
        else if (eqx2(s_p2,2'b1x))                                     r = 2'b01;
        else if (eqx2(s_ps,2'bx1))                                     r = 2'b01;
        else if (eqx2(s_p1,2'bxx))                                     r = 2'b01;
      end

      // piso 2 (010)
      3'b010: begin
        if      (eqx2(s_ps,2'b0x) || eqx2(s_p1,2'b0x))                 r = 2'b10;
        else if (eqx2(s_ps,2'b1x) || eqx2(s_p3,2'b1x))                 r = 2'b10;
        else if (eqx2(s_ps,2'bx1) || eqx2(s_p3,2'bx1))                 r = 2'b11;
        else if (eqx2(s_p3,2'b1x))                                     r = 2'b01;
        else if (eqx2(s_p1,2'bx1))                                     r = 2'b01;
        else if (eqx2(s_p2,2'bxx))                                     r = 2'b01;
      end

      // piso 3 (011)
      3'b011: begin
        if      (eqx2(s_ps,2'b0x) || eqx2(s_p1,2'b0x) || eqx2(s_p2,2'b0x)) r = 2'b10;
        else if (eqx2(s_ps,2'b1x) || eqx2(s_p1,2'b1x))                 r = 2'b10;
        else if (eqx2(s_ps,2'bx1) || eqx2(s_p1,2'bx1))                 r = 2'b11;
        else if (eqx2(s_p4,2'b1x))                                     r = 2'b01;
        else if (eqx2(s_p2,2'bx1))                                     r = 2'b01;
        else if (eqx2(s_p3,2'bxx))                                     r = 2'b01;
      end

      // piso 4 (100)
      3'b100: begin
        if      (eqx2(s_ps,2'b0x) || eqx2(s_p1,2'b0x) || eqx2(s_p2,2'b0x) || eqx2(s_p3,2'b0x)) r = 2'b10;
        else if (eqx2(s_p4,2'b0x))                                     r = 2'b01;
        else if (eqx2(s_p4,2'b1x))                                     r = 2'b00;
      end

      default: /* hold */ ;
    endcase
    return r;
  endfunction

  // Golden check: accion equals the priority-accurate next-state spec
  property p_accion_spec;
    disable iff (!FSM_ready_in)
    $past(FSM_ready_in) |->
      (accion == exp_next($past(piso_actual),
                          $past(solicitud_ps), $past(solicitud_p1),
                          $past(solicitud_p2), $past(solicitud_p3),
                          $past(solicitud_p4), $past(accion)));
  endproperty
  assert property (p_accion_spec);

  // Output must be 2-state when enabled
  assert property (disable iff (!FSM_ready_in)
                   $past(FSM_ready_in) |->
                   !$isunknown(accion));

  // Hold on unsupported floors (101-111)
  assert property (disable iff (!FSM_ready_in)
                   $past(FSM_ready_in) && (piso_actual inside {3'b101,3'b110,3'b111}) |->
                   (accion == $past(accion)));

  // --------------------------------
  // Concise functional coverage
  // --------------------------------

  // piso 0 coverage: each final accion
  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b000 && eqx2($past(solicitud_ps),2'bx1) |->
    (accion==2'b00));

  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b000 && eqx2($past(solicitud_ps),2'bx0) &&
    !(eqx2($past(solicitud_p1),2'bx0)||eqx2($past(solicitud_p2),2'bx0)||eqx2($past(solicitud_p3),2'bx0)||eqx2($past(solicitud_p4),2'bx0)) |->
    (accion==2'b01));

  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b000 &&
    (eqx2($past(solicitud_p1),2'bx0)||eqx2($past(solicitud_p2),2'bx0)||eqx2($past(solicitud_p3),2'bx0)||eqx2($past(solicitud_p4),2'bx0)) |->
    (accion==2'b10));

  // piso 1: observe 10, 11, 01 outcomes
  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b001 &&
    (eqx2($past(solicitud_ps),2'b0x) || eqx2($past(solicitud_p3),2'b1x) || eqx2($past(solicitud_p4),2'b1x)) |->
    (accion==2'b10));

  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b001 &&
    !(eqx2($past(solicitud_ps),2'b0x) || eqx2($past(solicitud_p3),2'b1x) || eqx2($past(solicitud_p4),2'b1x)) &&
    (eqx2($past(solicitud_p3),2'bx1) || eqx2($past(solicitud_p4),2'bx1)) |->
    (accion==2'b11));

  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b001 &&
    !(eqx2($past(solicitud_ps),2'b0x) || eqx2($past(solicitud_p3),2'b1x) || eqx2($past(solicitud_p4),2'b1x) ||
      eqx2($past(solicitud_p3),2'bx1) || eqx2($past(solicitud_p4),2'bx1)) &&
    (eqx2($past(solicitud_p2),2'b1x) || eqx2($past(solicitud_ps),2'bx1) || eqx2($past(solicitud_p1),2'bxx)) |->
    (accion==2'b01));

  // piso 2: observe 10, 11, 01 outcomes
  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b010 &&
    (eqx2($past(solicitud_ps),2'b0x) || eqx2($past(solicitud_p1),2'b0x) || eqx2($past(solicitud_ps),2'b1x) || eqx2($past(solicitud_p3),2'b1x)) |->
    (accion==2'b10));

  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b010 &&
    !(eqx2($past(solicitud_ps),2'b0x) || eqx2($past(solicitud_p1),2'b0x) || eqx2($past(solicitud_ps),2'b1x) || eqx2($past(solicitud_p3),2'b1x)) &&
    (eqx2($past(solicitud_ps),2'bx1) || eqx2($past(solicitud_p3),2'bx1)) |->
    (accion==2'b11));

  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b010 &&
    !(eqx2($past(solicitud_ps),2'b0x) || eqx2($past(solicitud_p1),2'b0x) || eqx2($past(solicitud_ps),2'b1x) || eqx2($past(solicitud_p3),2'b1x) ||
      eqx2($past(solicitud_ps),2'bx1) || eqx2($past(solicitud_p3),2'bx1)) &&
    (eqx2($past(solicitud_p3),2'b1x) || eqx2($past(solicitud_p1),2'bx1) || eqx2($past(solicitud_p2),2'bxx)) |->
    (accion==2'b01));

  // piso 3: observe 10, 11, 01 outcomes
  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b011 &&
    (eqx2($past(solicitud_ps),2'b0x) || eqx2($past(solicitud_p1),2'b0x) || eqx2($past(solicitud_p2),2'b0x) ||
     eqx2($past(solicitud_ps),2'b1x) || eqx2($past(solicitud_p1),2'b1x)) |->
    (accion==2'b10));

  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b011 &&
    !(eqx2($past(solicitud_ps),2'b0x) || eqx2($past(solicitud_p1),2'b0x) || eqx2($past(solicitud_p2),2'b0x) ||
      eqx2($past(solicitud_ps),2'b1x) || eqx2($past(solicitud_p1),2'b1x)) &&
    (eqx2($past(solicitud_ps),2'bx1) || eqx2($past(solicitud_p1),2'bx1)) |->
    (accion==2'b11));

  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b011 &&
    !(eqx2($past(solicitud_ps),2'b0x) || eqx2($past(solicitud_p1),2'b0x) || eqx2($past(solicitud_p2),2'b0x) ||
      eqx2($past(solicitud_ps),2'b1x) || eqx2($past(solicitud_p1),2'b1x) ||
      eqx2($past(solicitud_ps),2'bx1) || eqx2($past(solicitud_p1),2'bx1)) &&
    (eqx2($past(solicitud_p4),2'b1x) || eqx2($past(solicitud_p2),2'bx1) || eqx2($past(solicitud_p3),2'bxx)) |->
    (accion==2'b01));

  // piso 4: observe 10, 01, 00
  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b100 &&
    (eqx2($past(solicitud_ps),2'b0x) || eqx2($past(solicitud_p1),2'b0x) || eqx2($past(solicitud_p2),2'b0x) || eqx2($past(solicitud_p3),2'b0x)) |->
    (accion==2'b10));

  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b100 &&
    !(eqx2($past(solicitud_ps),2'b0x) || eqx2($past(solicitud_p1),2'b0x) || eqx2($past(solicitud_p2),2'b0x) || eqx2($past(solicitud_p3),2'b0x)) &&
    eqx2($past(solicitud_p4),2'b0x) |->
    (accion==2'b01));

  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b100 &&
    !(eqx2($past(solicitud_ps),2'b0x) || eqx2($past(solicitud_p1),2'b0x) || eqx2($past(solicitud_p2),2'b0x) || eqx2($past(solicitud_p3),2'b0x) ||
      eqx2($past(solicitud_p4),2'b0x)) &&
    eqx2($past(solicitud_p4),2'b1x) |->
    (accion==2'b00));

  // Priority override examples (ensure last-wins behavior is exercised)
  // piso 0: ps==x0 AND p1==x0 -> final 10 (override 01)
  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b000 &&
    eqx2($past(solicitud_ps),2'bx0) && eqx2($past(solicitud_p1),2'bx0) |->
    (accion==2'b10));

  // piso 1: p2==1x AND p3==1x -> final 10 (override 01 from p2==1x)
  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    $past(piso_actual)==3'b001 &&
    eqx2($past(solicitud_p2),2'b1x) && eqx2($past(solicitud_p3),2'b1x) |->
    (accion==2'b10));

  // Generic "hold" coverage
  cover property (disable iff (!FSM_ready_in)
    $past(FSM_ready_in) &&
    (accion == $past(accion)));

endmodule

// Bind into the DUT
bind VerificadorSentidoMovimiento VerificadorSentidoMovimiento_sva sva_i
(
  ._clk_(_clk_),
  .FSM_ready_in(FSM_ready_in),
  .piso_actual(piso_actual),
  .solicitud_ps(solicitud_ps),
  .solicitud_p1(solicitud_p1),
  .solicitud_p2(solicitud_p2),
  .solicitud_p3(solicitud_p3),
  .solicitud_p4(solicitud_p4),
  .accion(accion)
);