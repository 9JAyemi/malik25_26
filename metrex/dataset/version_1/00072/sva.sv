// SVA for teclado: concise, high-quality checks + coverage
// Bind this module to the DUT. Provide a sampling clock from TB.
module teclado_sva (
  input  logic        clk,     // sampling clock
  input  logic [7:0]  ps2_data,
  input  logic [4:0]  val,
  input  logic [2:0]  control,
  input  logic [7:0]  leds
);

  // Control encodings (mirror DUT)
  localparam CTRL_NUMERO    = 3'd1;
  localparam CTRL_ENTER     = 3'd2;
  localparam CTRL_FLECHA    = 3'd3;
  localparam CTRL_OPERACION = 3'd4;

  // PS/2 keycodes (mirror DUT)
  localparam CERO   = 8'h45, UNO  = 8'h16, DOS  = 8'h1E, TRES = 8'h26, CUATRO = 8'h25;
  localparam CINCO  = 8'h2E, SEIS = 8'h36, SIETE= 8'h3D, OCHO = 8'h3E, NUEVE  = 8'h46;
  localparam A      = 8'h1C, B    = 8'h32, C    = 8'h21, D    = 8'h23, E      = 8'h24, F = 8'h2B;
  localparam O      = 8'h44, Y    = 8'h35, SUMA = 8'h1B, RESTA= 8'h2D, MUL    = 8'h3A;
  localparam ENTER  = 8'h5A;
  localparam ARRIBA = 8'h75, ABAJO= 8'h72, IZQUIERDA = 8'h6B, DERECHA = 8'h74;

  // Default clocking for SVA
  default clocking cb @(posedge clk); endclocking

  // Basic invariants
  // LEDs mirror outputs
  a_leds_mirror: assert property (leds[4:0] == val && leds[7:5] == control);

  // Legal control values only
  a_control_legal: assert property (control inside {3'd0, CTRL_NUMERO, CTRL_ENTER, CTRL_FLECHA, CTRL_OPERACION});

  // val range always within 0..25
  a_val_range: assert property (val inside {[5'd0:5'd25]});

  // Category consistency: val -> control
  a_val_to_ctrl_num:  assert property ((val inside {[5'd0:5'd15]}) |-> control == CTRL_NUMERO);
  a_val_to_ctrl_ent:  assert property ((val == 5'd16)             |-> control == CTRL_ENTER);
  a_val_to_ctrl_fle:  assert property ((val inside {[5'd17:5'd20]})|-> control == CTRL_FLECHA);
  a_val_to_ctrl_op:   assert property ((val inside {[5'd21:5'd25]})|-> control == CTRL_OPERACION);
  a_ctrl0_val0:       assert property ((control == 3'd0)           |-> val == 5'd0);

  // Default mapping when ps2_data not a known key (and not X/Z)
  a_default_unknown_key: assert property (
    (! (ps2_data inside {
        CERO,UNO,DOS,TRES,CUATRO,CINCO,SEIS,SIETE,OCHO,NUEVE,
        A,B,C,D,E,F,
        SUMA,RESTA,MUL,Y,O,
        ENTER,
        ARRIBA,ABAJO,IZQUIERDA,DERECHA
      }) && !$isunknown(ps2_data)) |-> ##0 (val == 5'd0 && control == 3'd0)
  );

  // Optional: if ps2_data has X/Z, outputs fall to default
  a_xprop_default: assert property ($isunknown(ps2_data) |-> ##0 (val == 5'd0 && control == 3'd0));

  // Per-key exact mapping assertions + coverage (concise via macro)
`define MAP(KEY, V, CTRL) \
  a_``KEY: assert property ( (ps2_data == KEY) |-> ##0 (val == V && control == CTRL) ); \
  c_``KEY: cover  property ( (ps2_data == KEY) ##0 (val == V && control == CTRL) );

  // Numbers 0..9
  `MAP(CERO    , 5'd0 , CTRL_NUMERO)
  `MAP(UNO     , 5'd1 , CTRL_NUMERO)
  `MAP(DOS     , 5'd2 , CTRL_NUMERO)
  `MAP(TRES    , 5'd3 , CTRL_NUMERO)
  `MAP(CUATRO  , 5'd4 , CTRL_NUMERO)
  `MAP(CINCO   , 5'd5 , CTRL_NUMERO)
  `MAP(SEIS    , 5'd6 , CTRL_NUMERO)
  `MAP(SIETE   , 5'd7 , CTRL_NUMERO)
  `MAP(OCHO    , 5'd8 , CTRL_NUMERO)
  `MAP(NUEVE   , 5'd9 , CTRL_NUMERO)

  // Hex A..F
  `MAP(A       , 5'd10, CTRL_NUMERO)
  `MAP(B       , 5'd11, CTRL_NUMERO)
  `MAP(C       , 5'd12, CTRL_NUMERO)
  `MAP(D       , 5'd13, CTRL_NUMERO)
  `MAP(E       , 5'd14, CTRL_NUMERO)
  `MAP(F       , 5'd15, CTRL_NUMERO)

  // ENTER
  `MAP(ENTER   , 5'd16, CTRL_ENTER)

  // Arrows
  `MAP(IZQUIERDA,5'd17, CTRL_FLECHA)
  `MAP(DERECHA , 5'd18, CTRL_FLECHA)
  `MAP(ARRIBA  , 5'd19, CTRL_FLECHA)
  `MAP(ABAJO   , 5'd20, CTRL_FLECHA)

  // Operations
  `MAP(SUMA    , 5'd21, CTRL_OPERACION)
  `MAP(RESTA   , 5'd22, CTRL_OPERACION)
  `MAP(MUL     , 5'd23, CTRL_OPERACION)
  `MAP(Y       , 5'd24, CTRL_OPERACION)
  `MAP(O       , 5'd25, CTRL_OPERACION)

  // Category coverage summaries
  c_numero:   cover property (control == CTRL_NUMERO);
  c_enter:    cover property (control == CTRL_ENTER);
  c_flecha:   cover property (control == CTRL_FLECHA);
  c_oper:     cover property (control == CTRL_OPERACION);
  c_default:  cover property (control == 3'd0 && val == 5'd0 &&
                              !(ps2_data inside {
                                CERO,UNO,DOS,TRES,CUATRO,CINCO,SEIS,SIETE,OCHO,NUEVE,
                                A,B,C,D,E,F,SUMA,RESTA,MUL,Y,O,ENTER,ARRIBA,ABAJO,IZQUIERDA,DERECHA
                              }));

`undef MAP
endmodule

// Bind example (hook clk from your TB)
// bind teclado teclado_sva u_teclado_sva (.* , .clk(tb_clk));