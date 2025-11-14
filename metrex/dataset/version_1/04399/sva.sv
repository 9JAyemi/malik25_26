// SVA for MarioScore24x1
// Bind this module to the DUT and connect a simulation clock/reset.
module MarioScore24x1_sva (
  input logic              clk,
  input logic              rst_n,
  // DUT ports
  input logic [7:0]        char_xy,
  input logic [3:0]        mario_lives,
  input logic [3:0]        level,
  input logic [11:0]       coins,
  input logic [7:0]        char_code
);
  default clocking cb @ (posedge clk); endclocking
  default disable iff (!rst_n)

  function automatic [7:0] enc_digit(input int d);
    return (d>=0 && d<=9) ? d[7:0] : 8'h00;
  endfunction
  function automatic int dec_digit(input int val, input int idx);
    case (idx)
      0: return val%10;
      1: return (val/10)%10;
      2: return (val/100)%10;
      default: return 0;
    endcase
  endfunction

  // Basic sanity
  assert property (!$isunknown({char_xy,mario_lives,level,coins}) |-> !$isunknown(char_code));
  assert property ($stable({char_xy,mario_lives,level,coins}) |-> $stable(char_code));

  // Static map: 0x00..0x06 -> 0x0A + char_xy
  assert property (char_xy inside {[8'h00:8'h06]} |-> char_code == (8'h0A + char_xy));

  // Lives @ 0x07
  assert property (char_xy==8'h07 |-> char_code == enc_digit(mario_lives));
  assert property (char_xy==8'h07 && (mario_lives>9) |-> char_code==8'h00);

  // Range 0x08..0x1F -> 0x0F
  assert property (char_xy inside {[8'h08:8'h1F]} |-> char_code==8'h0F);

  // Specific constants
  assert property (char_xy==8'h20 |-> char_code==8'h11);
  assert property (char_xy==8'h21 |-> char_code==8'h0F);
  assert property (char_xy==8'h22 |-> char_code==8'h10);

  // Coins digits @ 0x23..0x25 always legal BCD
  assert property ((char_xy inside {8'h23,8'h24,8'h25}) |-> (char_code inside {[8'h00:8'h09]}));
  // Exact decimal when coins <= 999
  assert property ((coins<=12'd999 && char_xy==8'h25) |-> char_code==enc_digit(dec_digit(coins,0)));
  assert property ((coins<=12'd999 && char_xy==8'h24) |-> char_code==enc_digit(dec_digit(coins,1)));
  assert property ((coins<=12'd999 && char_xy==8'h23) |-> char_code==enc_digit(dec_digit(coins,2)));

  // Range 0x26..0x3D -> 0x0F
  assert property (char_xy inside {[8'h26:8'h3D]} |-> char_code==8'h0F);

  // Tail constants
  assert property (char_xy==8'h3E |-> char_code==8'h12);
  assert property (char_xy==8'h3F |-> char_code==8'h13);
  assert property (char_xy==8'h40 |-> char_code==8'h14);
  assert property (char_xy==8'h41 |-> char_code==8'h13);
  assert property (char_xy==8'h42 |-> char_code==8'h12);
  assert property (char_xy==8'h43 |-> char_code==8'h0F);

  // Level @ 0x44
  assert property (char_xy==8'h44 |-> char_code==enc_digit(level));
  assert property (char_xy==8'h44 && (level>9) |-> char_code==8'h00);

  // Default > 0x44 -> 0xFF
  assert property (char_xy > 8'h44 |-> char_code==8'hFF);

  // Coverage (key edges and cases)
  cover property (char_xy inside {[8'h00:8'h06]});
  cover property (char_xy==8'h07 && mario_lives==4'd0);
  cover property (char_xy==8'h07 && mario_lives==4'd9);
  cover property (char_xy==8'h07 && mario_lives>9);
  cover property (char_xy==8'h23 && coins==12'd0);
  cover property (char_xy==8'h25 && coins==12'd9);
  cover property (char_xy==8'h24 && coins==12'd10);
  cover property (char_xy==8'h23 && coins==12'd99);
  cover property (char_xy==8'h23 && coins==12'd100);
  cover property (char_xy==8'h25 && coins==12'd999);
  cover property (char_xy==8'h25 && coins==12'd1000);
  cover property (char_xy==8'h25 && coins==12'd4095);
  cover property (char_xy==8'h20);
  cover property (char_xy==8'h22);
  cover property (char_xy==8'h3E);
  cover property (char_xy==8'h3F);
  cover property (char_xy==8'h40);
  cover property (char_xy==8'h41);
  cover property (char_xy==8'h42);
  cover property (char_xy==8'h44 && level==4'd9);
  cover property (char_xy > 8'h44);
endmodule

// Example bind (edit clk/rst_n to your env):
// bind MarioScore24x1 MarioScore24x1_sva u_MarioScore24x1_sva ( .clk(tb_clk), .rst_n(tb_rst_n), .* );