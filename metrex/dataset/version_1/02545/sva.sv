// SVA checker for Decodificador
// - Exhaustive functional check via golden function
// - X/Z checks
// - No-glitch check (outputs don’t change while input stable)
// - Simple coverage for all decoded Cuenta values + default

module Decodificador_sva (
  input logic [6:0] Cuenta,
  input logic [7:0] catodo1,
  input logic [7:0] catodo2,
  input logic [7:0] catodo3,
  input logic [7:0] catodo4
);

  // Golden model (mirrors DUT truth-table)
  function automatic void exp_outputs(
    input  logic [6:0] c,
    output logic [7:0] e1, e2, e3, e4
  );
    unique case (c)
      7'b0000000: begin e1=8'b00000011; e2=8'b00000011; e3=8'b00000011; e4=8'b00000011; end
      7'b0000001: begin e1=8'b10011111; e2=8'b00000011; e3=8'b00000011; e4=8'b00000011; end
      7'b0000010: begin e1=8'b00100101; e2=8'b00000011; e3=8'b00000011; e4=8'b00000011; end
      7'b0000011: begin e1=8'b00001101; e2=8'b00000011; e3=8'b00000011; e4=8'b00000011; end
      7'b0000100: begin e1=8'b10011001; e2=8'b00000011; e3=8'b00000011; e4=8'b00000011; end
      7'b0000101: begin e1=8'b01001001; e2=8'b00000011; e3=8'b00000011; e4=8'b00000011; end
      7'b0000110: begin e1=8'b01000001; e2=8'b00000011; e3=8'b00000011; e4=8'b00000011; end
      7'b0000111: begin e1=8'b00011111; e2=8'b00000011; e3=8'b00000011; e4=8'b00000011; end
      7'b0001000: begin e1=8'b00000001; e2=8'b00000011; e3=8'b00000011; e4=8'b00000011; end
      7'b0001001: begin e1=8'b00011001; e2=8'b00000011; e3=8'b00000011; e4=8'b00000011; end
      7'b0001010: begin e1=8'b00000011; e2=8'b10011111; e3=8'b00000011; e4=8'b00000011; end
      7'b0001011: begin e1=8'b10011111; e2=8'b10011111; e3=8'b00000011; e4=8'b00000011; end
      7'b0001100: begin e1=8'b00100101; e2=8'b10011111; e3=8'b00000011; e4=8'b00000011; end
      7'b0001101: begin e1=8'b00001101; e2=8'b10011111; e3=8'b00000011; e4=8'b00000011; end
      7'b0001110: begin e1=8'b10011001; e2=8'b10011111; e3=8'b00000011; e4=8'b00000011; end
      7'b0001111: begin e1=8'b01001001; e2=8'b10011111; e3=8'b00000011; e4=8'b00000011; end
      default:    begin e1=8'b10011111; e2=8'b10011111; e3=8'b10011111; e4=8'b10011111; end
    endcase
  endfunction

  // Immediate assertions (clockless, combinational)
  always_comb begin
    logic [7:0] e1, e2, e3, e4;
    exp_outputs(Cuenta, e1, e2, e3, e4);

    // Functional equivalence
    assert ({catodo1,catodo2,catodo3,catodo4} === {e1,e2,e3,e4})
      else $error("Decodificador mismatch: Cuenta=%0b got=%h %h %h %h exp=%h %h %h %h",
                  Cuenta, catodo1,catodo2,catodo3,catodo4, e1,e2,e3,e4);

    // No X/Z on outputs
    assert (!$isunknown({catodo1,catodo2,catodo3,catodo4}))
      else $error("Decodificador X/Z on outputs for Cuenta=%0b", Cuenta);

    // Coverage of all decoded values and default region
    cover (Cuenta == 7'b0000000);
    cover (Cuenta == 7'b0000001);
    cover (Cuenta == 7'b0000010);
    cover (Cuenta == 7'b0000011);
    cover (Cuenta == 7'b0000100);
    cover (Cuenta == 7'b0000101);
    cover (Cuenta == 7'b0000110);
    cover (Cuenta == 7'b0000111);
    cover (Cuenta == 7'b0001000);
    cover (Cuenta == 7'b0001001);
    cover (Cuenta == 7'b0001010);
    cover (Cuenta == 7'b0001011);
    cover (Cuenta == 7'b0001100);
    cover (Cuenta == 7'b0001101);
    cover (Cuenta == 7'b0001110);
    cover (Cuenta == 7'b0001111);
    cover (Cuenta > 7'd15); // default region
  end

  // Simple glitch check across time: outputs must not change if input is stable
  // (uses static storage; ignores initial sample)
  static bit init_done;
  static logic [6:0] prev_c;
  static logic [31:0] prev_o;
  always @(*) begin
    logic [31:0] cur_o = {catodo1,catodo2,catodo3,catodo4};
    if (init_done && (Cuenta === prev_c)) begin
      assert (cur_o === prev_o)
        else $error("Decodificador glitch: outputs changed while Cuenta stable (%0b)", Cuenta);
    end
    prev_c   = Cuenta;
    prev_o   = cur_o;
    init_done = 1'b1;
  end

endmodule

// Bind into the DUT
bind Decodificador Decodificador_sva u_decodificador_sva (
  .Cuenta (Cuenta),
  .catodo1(catodo1),
  .catodo2(catodo2),
  .catodo3(catodo3),
  .catodo4(catodo4)
);