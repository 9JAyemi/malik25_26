// SVA checker for teclado. Bind this file to the DUT.
// Focuses on full mapping correctness, category/range guards, mirroring, and coverage.

module teclado_sva(
  input  logic [7:0] ps2_data,
  input  logic [4:0] val,
  input  logic [2:0] control,
  input  logic [7:0] leds
);

  // Control encodings
  localparam logic [2:0] CTRL_NUMERO    = 3'd1;
  localparam logic [2:0] CTRL_ENTER     = 3'd2;
  localparam logic [2:0] CTRL_FLECHA    = 3'd3;
  localparam logic [2:0] CTRL_OPERACION = 3'd4;

  // Key codes
  localparam logic [7:0] CERO   = 8'h45;
  localparam logic [7:0] UNO    = 8'h16;
  localparam logic [7:0] DOS    = 8'h1E;
  localparam logic [7:0] TRES   = 8'h26;
  localparam logic [7:0] CUATRO = 8'h25;
  localparam logic [7:0] CINCO  = 8'h2E;
  localparam logic [7:0] SEIS   = 8'h36;
  localparam logic [7:0] SIETE  = 8'h3D;
  localparam logic [7:0] OCHO   = 8'h3E;
  localparam logic [7:0] NUEVE  = 8'h46;
  localparam logic [7:0] A      = 8'h1C;
  localparam logic [7:0] B      = 8'h32;
  localparam logic [7:0] C      = 8'h21;
  localparam logic [7:0] D      = 8'h23;
  localparam logic [7:0] E      = 8'h24;
  localparam logic [7:0] F      = 8'h2B;
  localparam logic [7:0] O      = 8'h44;
  localparam logic [7:0] Y      = 8'h35;
  localparam logic [7:0] SUMA   = 8'h1B;
  localparam logic [7:0] RESTA  = 8'h2D;
  localparam logic [7:0] MUL    = 8'h3A;
  localparam logic [7:0] ENTER  = 8'h5A;
  localparam logic [7:0] ARRIBA    = 8'h75;
  localparam logic [7:0] ABAJO     = 8'h72;
  localparam logic [7:0] IZQUIERDA = 8'h6B;
  localparam logic [7:0] DERECHA   = 8'h74;

  function automatic bit is_defined_code(input logic [7:0] d);
    return (d inside {
      CERO,UNO,DOS,TRES,CUATRO,CINCO,SEIS,SIETE,OCHO,NUEVE,
      A,B,C,D,E,F,
      SUMA,RESTA,MUL,Y,O,
      ENTER,
      ARRIBA,ABAJO,IZQUIERDA,DERECHA
    });
  endfunction

  always_comb begin
    // Structural/mirroring checks
    assert (leds[4:0] == val) else $error("leds[4:0] must equal val");
    assert (leds[7:5] == control) else $error("leds[7:5] must equal control");

    // No X/Z on outputs
    assert (!$isunknown({val,control,leds})) else $error("X/Z on outputs");

    // Control encoding is legal
    assert (control inside {3'd0,CTRL_NUMERO,CTRL_ENTER,CTRL_FLECHA,CTRL_OPERACION})
      else $error("Illegal control value %0d", control);

    // Category/value guards
    if (control == CTRL_NUMERO)    assert (val inside {[5'd0:5'd15]}) else $error("NUMERO val out of range");
    if (control == CTRL_ENTER)     assert (val == 5'd16)              else $error("ENTER val must be 16");
    if (control == CTRL_FLECHA)    assert (val inside {[5'd17:5'd20]})else $error("FLECHA val out of range");
    if (control == CTRL_OPERACION) assert (val inside {5'd21,5'd22,5'd23,5'd24,5'd25})
                                   else $error("OPERACION val out of set");

    // Forward mapping: ps2_data -> (val, control)
    unique case (ps2_data)
      CERO:      assert (val==5'd0  && control==CTRL_NUMERO)      else $error("CERO map");
      UNO:       assert (val==5'd1  && control==CTRL_NUMERO)      else $error("UNO map");
      DOS:       assert (val==5'd2  && control==CTRL_NUMERO)      else $error("DOS map");
      TRES:      assert (val==5'd3  && control==CTRL_NUMERO)      else $error("TRES map");
      CUATRO:    assert (val==5'd4  && control==CTRL_NUMERO)      else $error("CUATRO map");
      CINCO:     assert (val==5'd5  && control==CTRL_NUMERO)      else $error("CINCO map");
      SEIS:      assert (val==5'd6  && control==CTRL_NUMERO)      else $error("SEIS map");
      SIETE:     assert (val==5'd7  && control==CTRL_NUMERO)      else $error("SIETE map");
      OCHO:      assert (val==5'd8  && control==CTRL_NUMERO)      else $error("OCHO map");
      NUEVE:     assert (val==5'd9  && control==CTRL_NUMERO)      else $error("NUEVE map");
      A:         assert (val==5'd10 && control==CTRL_NUMERO)      else $error("A map");
      B:         assert (val==5'd11 && control==CTRL_NUMERO)      else $error("B map");
      C:         assert (val==5'd12 && control==CTRL_NUMERO)      else $error("C map");
      D:         assert (val==5'd13 && control==CTRL_NUMERO)      else $error("D map");
      E:         assert (val==5'd14 && control==CTRL_NUMERO)      else $error("E map");
      F:         assert (val==5'd15 && control==CTRL_NUMERO)      else $error("F map");
      SUMA:      assert (val==5'd21 && control==CTRL_OPERACION)   else $error("SUMA map");
      RESTA:     assert (val==5'd22 && control==CTRL_OPERACION)   else $error("RESTA map");
      MUL:       assert (val==5'd23 && control==CTRL_OPERACION)   else $error("MUL map");
      Y:         assert (val==5'd24 && control==CTRL_OPERACION)   else $error("Y map");
      O:         assert (val==5'd25 && control==CTRL_OPERACION)   else $error("O map");
      ENTER:     assert (val==5'd16 && control==CTRL_ENTER)       else $error("ENTER map");
      ARRIBA:    assert (val==5'd19 && control==CTRL_FLECHA)      else $error("ARRIBA map");
      ABAJO:     assert (val==5'd20 && control==CTRL_FLECHA)      else $error("ABAJO map");
      IZQUIERDA: assert (val==5'd17 && control==CTRL_FLECHA)      else $error("IZQUIERDA map");
      DERECHA:   assert (val==5'd18 && control==CTRL_FLECHA)      else $error("DERECHA map");
      default:   assert (val==5'd0  && control==3'd0)             else $error("Default map");
    endcase

    // Default iff undefined code
    if (!is_defined_code(ps2_data)) begin
      assert (val==5'd0 && control==3'd0) else $error("Undefined code must select default");
    end else begin
      assert (control != 3'd0) else $error("Defined code must not select default control");
    end

    // Reverse mapping (injectivity within each category)
    if (control == CTRL_NUMERO) begin
      unique case (val)
        5'd0:  assert (ps2_data==CERO);
        5'd1:  assert (ps2_data==UNO);
        5'd2:  assert (ps2_data==DOS);
        5'd3:  assert (ps2_data==TRES);
        5'd4:  assert (ps2_data==CUATRO);
        5'd5:  assert (ps2_data==CINCO);
        5'd6:  assert (ps2_data==SEIS);
        5'd7:  assert (ps2_data==SIETE);
        5'd8:  assert (ps2_data==OCHO);
        5'd9:  assert (ps2_data==NUEVE);
        5'd10: assert (ps2_data==A);
        5'd11: assert (ps2_data==B);
        5'd12: assert (ps2_data==C);
        5'd13: assert (ps2_data==D);
        5'd14: assert (ps2_data==E);
        5'd15: assert (ps2_data==F);
        default: ;
      endcase
    end
    if (control == CTRL_OPERACION) begin
      unique case (val)
        5'd21: assert (ps2_data==SUMA);
        5'd22: assert (ps2_data==RESTA);
        5'd23: assert (ps2_data==MUL);
        5'd24: assert (ps2_data==Y);
        5'd25: assert (ps2_data==O);
        default: ;
      endcase
    end
    if (control == CTRL_ENTER)   assert (ps2_data==ENTER);
    if (control == CTRL_FLECHA) begin
      unique case (val)
        5'd17: assert (ps2_data==IZQUIERDA);
        5'd18: assert (ps2_data==DERECHA);
        5'd19: assert (ps2_data==ARRIBA);
        5'd20: assert (ps2_data==ABAJO);
        default: ;
      endcase
    end

    // Immediate functional coverage (hit all codes and categories)
    cover (ps2_data==CERO);
    cover (ps2_data==UNO);
    cover (ps2_data==DOS);
    cover (ps2_data==TRES);
    cover (ps2_data==CUATRO);
    cover (ps2_data==CINCO);
    cover (ps2_data==SEIS);
    cover (ps2_data==SIETE);
    cover (ps2_data==OCHO);
    cover (ps2_data==NUEVE);
    cover (ps2_data==A);
    cover (ps2_data==B);
    cover (ps2_data==C);
    cover (ps2_data==D);
    cover (ps2_data==E);
    cover (ps2_data==F);
    cover (ps2_data==SUMA);
    cover (ps2_data==RESTA);
    cover (ps2_data==MUL);
    cover (ps2_data==Y);
    cover (ps2_data==O);
    cover (ps2_data==ENTER);
    cover (ps2_data==ARRIBA);
    cover (ps2_data==ABAJO);
    cover (ps2_data==IZQUIERDA);
    cover (ps2_data==DERECHA);
    cover (!is_defined_code(ps2_data)); // default path
    cover (control==CTRL_NUMERO);
    cover (control==CTRL_ENTER);
    cover (control==CTRL_FLECHA);
    cover (control==CTRL_OPERACION);
  end

endmodule

// Bind into the DUT
bind teclado teclado_sva teclado_sva_i(
  .ps2_data(ps2_data),
  .val(val),
  .control(control),
  .leds(leds)
);