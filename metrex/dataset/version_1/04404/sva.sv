// SVA checker for Contador_AD_Minutos
module Contador_AD_Minutos_sva #(parameter int N=6, X=59) (
  input  logic                 clk,
  input  logic                 rst,
  input  logic [7:0]           estado,
  input  logic [1:0]           en,
  input  logic [7:0]           Cambio,
  input  logic                 got_data,
  input  logic [N-1:0]         Cuenta
);
  localparam logic [7:0] ESTADO_L = 8'h6C;
  localparam logic [7:0] ESTADO_U = 8'h75;
  localparam logic [7:0] CMD_INC  = 8'h73;
  localparam logic [7:0] CMD_DEC  = 8'h72;

  default clocking cb @(posedge clk); endclocking

  let active  = (en == 2'd1) && (estado == ESTADO_L || estado == ESTADO_U);
  let inc_cmd = active && got_data && (Cambio == CMD_INC);
  let dec_cmd = active && got_data && (Cambio == CMD_DEC);

  // Parameter sanity
  initial assert (X < (1<<N)) else $error("X=%0d must be < 2^N=%0d", X, (1<<N));

  // Reset drives counter to 0 (synchronous)
  assert property (cb rst |-> (Cuenta == '0));

  // Counter always within 0..X
  assert property (cb disable iff (rst) (Cuenta <= X));

  // No change unless a valid command occurs in an active state with got_data
  assert property (cb disable iff (rst) (!(inc_cmd || dec_cmd) |-> $stable(Cuenta)));

  // Increment behavior (+1 or wrap to 0)
  assert property (cb disable iff (rst) (inc_cmd && $past(Cuenta) != X) |-> Cuenta == $past(Cuenta) + 1);
  assert property (cb disable iff (rst) (inc_cmd && $past(Cuenta) == X) |-> Cuenta == '0);

  // Decrement behavior (-1 or wrap to X)
  assert property (cb disable iff (rst) (dec_cmd && $past(Cuenta) != 0) |-> Cuenta == $past(Cuenta) - 1);
  assert property (cb disable iff (rst) (dec_cmd && $past(Cuenta) == 0) |-> Cuenta == X);

  // Coverage
  cover property (cb disable iff (rst) inc_cmd);
  cover property (cb disable iff (rst) dec_cmd);
  cover property (cb disable iff (rst) ($past(Cuenta) == X) && inc_cmd); // wrap up
  cover property (cb disable iff (rst) ($past(Cuenta) == 0) && dec_cmd); // wrap down
  cover property (cb disable iff (rst) (active && estado == ESTADO_L && (inc_cmd || dec_cmd)));
  cover property (cb disable iff (rst) (active && estado == ESTADO_U && (inc_cmd || dec_cmd)));
  cover property (cb disable iff (rst) (active && got_data && !(Cambio == CMD_INC || Cambio == CMD_DEC))); // ignored cmd
  cover property (cb disable iff (rst) (!active)); // inactive hold
endmodule

// Bind into DUT
bind Contador_AD_Minutos Contador_AD_Minutos_sva #(.N(N), .X(X)) Contador_AD_Minutos_sva_i (
  .clk(clk),
  .rst(rst),
  .estado(estado),
  .en(en),
  .Cambio(Cambio),
  .got_data(got_data),
  .Cuenta(Cuenta)
);