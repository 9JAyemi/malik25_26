// SVA checker for module inicial
module inicial_sva (
  input logic SW4, SW3, SW2, SW1, SW0, CLK,
  input logic LEDG, LEDR,
  input logic [6:0] HEX0
);

  default clocking cb @(posedge CLK); endclocking

  localparam logic [6:0]
    SEG_0 = 7'b1000000,
    SEG_1 = 7'b1111001,
    SEG_2 = 7'b0100100,
    SEG_3 = 7'b0110000,
    SEG_4 = 7'b0011001,
    SEG_5 = 7'b0010010,
    SEG_6 = 7'b0000010,
    SEG_7 = 7'b1111000,
    SEG_8 = 7'b0000000,
    SEG_9 = 7'b0010000,
    SEG_E = 7'b1001111;

  function automatic logic [6:0] exp_hex (logic [4:0] sw);
    unique case (sw)
      5'b00000: exp_hex = SEG_0;
      5'b00001: exp_hex = SEG_1;
      5'b00010: exp_hex = SEG_2;
      5'b00011: exp_hex = SEG_3;
      5'b00100: exp_hex = SEG_4;
      5'b00101: exp_hex = SEG_5;
      5'b00110: exp_hex = SEG_6;
      5'b00111: exp_hex = SEG_7;
      5'b01000: exp_hex = SEG_8;
      5'b01001: exp_hex = SEG_9;
      default : exp_hex = SEG_E;
    endcase
  endfunction

  // Functional mapping check
  assert property (HEX0 == exp_hex({SW4,SW3,SW2,SW1,SW0}))
    else $error("HEX0 mismatch sw=%b hex=%b exp=%b",
                {SW4,SW3,SW2,SW1,SW0}, HEX0, exp_hex({SW4,SW3,SW2,SW1,SW0}));

  // LED correctness and mutual exclusivity
  assert property (LEDG === ~SW0);
  assert property (LEDR ===  SW0);
  assert property ((LEDG ^ LEDR) === 1'b1);

  // Outputs known
  assert property (!$isunknown({LEDG, LEDR, HEX0}))
    else $error("X/Z on outputs");

  // Coverage: each code path 0..9 and default 'E'
  cover property (({SW4,SW3,SW2,SW1,SW0}==5'b00000) && (HEX0==SEG_0));
  cover property (({SW4,SW3,SW2,SW1,SW0}==5'b00001) && (HEX0==SEG_1));
  cover property (({SW4,SW3,SW2,SW1,SW0}==5'b00010) && (HEX0==SEG_2));
  cover property (({SW4,SW3,SW2,SW1,SW0}==5'b00011) && (HEX0==SEG_3));
  cover property (({SW4,SW3,SW2,SW1,SW0}==5'b00100) && (HEX0==SEG_4));
  cover property (({SW4,SW3,SW2,SW1,SW0}==5'b00101) && (HEX0==SEG_5));
  cover property (({SW4,SW3,SW2,SW1,SW0}==5'b00110) && (HEX0==SEG_6));
  cover property (({SW4,SW3,SW2,SW1,SW0}==5'b00111) && (HEX0==SEG_7));
  cover property (({SW4,SW3,SW2,SW1,SW0}==5'b01000) && (HEX0==SEG_8));
  cover property (({SW4,SW3,SW2,SW1,SW0}==5'b01001) && (HEX0==SEG_9));
  cover property (({SW4,SW3,SW2,SW1,SW0} inside {[5'b01010:5'b11111]}) && (HEX0==SEG_E));

  // Coverage: SW0 edges reflect on LEDs
  cover property ($rose(SW0) and (LEDG==1'b0) and (LEDR==1'b1));
  cover property ($fell(SW0) and (LEDG==1'b1) and (LEDR==1'b0));

endmodule

bind inicial inicial_sva sva(.SW4(SW4),.SW3(SW3),.SW2(SW2),.SW1(SW1),.SW0(SW0),
                             .CLK(CLK),.LEDG(LEDG),.LEDR(LEDR),.HEX0(HEX0));