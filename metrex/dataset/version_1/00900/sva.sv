// SVA for Contador_AD_Dia
module Contador_AD_Dia_sva #(parameter int N=7, X=99) (
  input clk,
  input rst,
  input [7:0] estado,
  input [1:0] en,
  input [7:0] Cambio,
  input got_data,
  input [N-1:0] Cuenta
);
  default clocking cb @(posedge clk); endclocking

  localparam [7:0] ST     = 8'h7D;
  localparam [7:0] INC_OP = 8'h73;
  localparam [7:0] DEC_OP = 8'h72;
  localparam [1:0] EN_GO  = 2'd2;

  wire gate = (en == EN_GO) && (estado == ST);

  // Reset behavior
  assert property (rst |=> (Cuenta == 1));

  // Value always in legal range (after reset)
  assert property (disable iff (rst) (Cuenta >= 1 && Cuenta <= X));

  // Hold when no valid operation
  assert property (disable iff (rst)
                   !(gate && got_data && (Cambio == INC_OP || Cambio == DEC_OP))
                   |-> (Cuenta == $past(Cuenta)));

  // Increment behavior with wrap
  assert property (disable iff (rst)
                   (gate && got_data && (Cambio == INC_OP))
                   |-> (Cuenta == (($past(Cuenta) == X) ? 1 : $past(Cuenta) + 1)));

  // Decrement behavior with wrap
  assert property (disable iff (rst)
                   (gate && got_data && (Cambio == DEC_OP))
                   |-> (Cuenta == (($past(Cuenta) == 1) ? X : $past(Cuenta) - 1)));

  // Any change must be due to a valid op under gate
  assert property (disable iff (rst || $past(rst))
                   $changed(Cuenta)
                   |-> (gate && got_data && (Cambio == INC_OP || Cambio == DEC_OP)));

  // No X/Z on output after reset
  assert property (disable iff (rst) !$isunknown(Cuenta));

  // Coverage
  cover property (disable iff (rst)
                  gate && got_data && (Cambio == INC_OP) &&
                  $past(Cuenta) inside {[1:X-1]} &&
                  Cuenta == $past(Cuenta) + 1);

  cover property (disable iff (rst)
                  gate && got_data && (Cambio == INC_OP) &&
                  $past(Cuenta) == X && Cuenta == 1);

  cover property (disable iff (rst)
                  gate && got_data && (Cambio == DEC_OP) &&
                  $past(Cuenta) inside {[2:X]} &&
                  Cuenta == $past(Cuenta) - 1);

  cover property (disable iff (rst)
                  gate && got_data && (Cambio == DEC_OP) &&
                  $past(Cuenta) == 1 && Cuenta == X);
endmodule

// Bind into DUT
bind Contador_AD_Dia Contador_AD_Dia_sva #(.N(N), .X(X)) Contador_AD_Dia_sva_i (
  .clk(clk), .rst(rst), .estado(estado), .en(en), .Cambio(Cambio), .got_data(got_data), .Cuenta(Cuenta)
);