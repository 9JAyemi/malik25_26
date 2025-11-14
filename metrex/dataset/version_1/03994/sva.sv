// SVA checker for module 'characters'.
// Bind this checker to your DUT and drive clk/rst_n from your environment.

module characters_sva
(
  input  logic        clk,
  input  logic        rst_n,
  input  logic [7:0]  select,
  input  logic [39:0] vec_char
);

  // Golden constant bitmaps (mirrors DUT)
  localparam logic [39:0] vect_char_a={5'b00000,5'b11110,5'b10001,5'b11110,5'b10000,5'b01110,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_b={5'b00000,5'b01111,5'b10001,5'b10001,5'b10011,5'b01101,5'b00001,5'b00001};
  localparam logic [39:0] vect_char_c={5'b00000,5'b01110,5'b10001,5'b00001,5'b00001,5'b01110,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_d={5'b00000,5'b11110,5'b10001,5'b10001,5'b11001,5'b10110,5'b10000,5'b10000};
  localparam logic [39:0] vect_char_e={5'b00000,5'b01110,5'b00001,5'b11111,5'b10001,5'b01110,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_f={5'b00000,5'b00010,5'b00010,5'b00010,5'b00111,5'b00010,5'b10010,5'b01100};
  localparam logic [39:0] vect_char_g={5'b00000,5'b01110,5'b10000,5'b11110,5'b10001,5'b10001,5'b11110,5'b00000};
  localparam logic [39:0] vect_char_h={5'b00000,5'b10001,5'b10001,5'b10001,5'b10011,5'b01101,5'b00001,5'b00001};
  localparam logic [39:0] vect_char_i={5'b00000,5'b01110,5'b00100,5'b00100,5'b00100,5'b00110,5'b00000,5'b00100};
  localparam logic [39:0] vect_char_j={5'b00000,5'b00110,5'b01001,5'b01000,5'b01000,5'b01100,5'b00000,5'b01000};
  localparam logic [39:0] vect_char_k={5'b00000,5'b01001,5'b00101,5'b00011,5'b00101,5'b01001,5'b00001,5'b00001};
  localparam logic [39:0] vect_char_l={5'b00000,5'b01110,5'b00100,5'b00100,5'b00100,5'b00100,5'b00100,5'b00110};
  localparam logic [39:0] vect_char_m={5'b00000,5'b10001,5'b10001,5'b10101,5'b10101,5'b01011,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_n={5'b00000,5'b10001,5'b10001,5'b10001,5'b10011,5'b01101,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_o={5'b00000,5'b01110,5'b10001,5'b10001,5'b10001,5'b01110,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_p={5'b00000,5'b00001,5'b00001,5'b01111,5'b10001,5'b01111,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_q={5'b00000,5'b10000,5'b10000,5'b11110,5'b11001,5'b10110,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_r={5'b00000,5'b00001,5'b00001,5'b00001,5'b10011,5'b01101,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_s={5'b00000,5'b01111,5'b10000,5'b01110,5'b00001,5'b01110,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_t={5'b00000,5'b01100,5'b10010,5'b00010,5'b00010,5'b00111,5'b00010,5'b00010};
  localparam logic [39:0] vect_char_u={5'b00000,5'b10110,5'b11001,5'b10001,5'b10001,5'b10001,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_v={5'b00000,5'b00100,5'b01010,5'b10001,5'b10001,5'b10001,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_w={5'b00000,5'b01010,5'b10101,5'b10101,5'b10001,5'b10001,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_x={5'b00000,5'b10001,5'b01010,5'b00100,5'b01010,5'b10001,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_y={5'b00000,5'b01110,5'b10000,5'b11110,5'b10001,5'b10001,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_z={5'b00000,5'b11111,5'b00010,5'b00100,5'b01000,5'b11111,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_E={5'b00000,5'b11111,5'b00001,5'b00001,5'b01111,5'b00001,5'b00001,5'b11111};
  localparam logic [39:0] vect_char_C={5'b00000,5'b01110,5'b10001,5'b00001,5'b00001,5'b00001,5'b10001,5'b01110};
  localparam logic [39:0] vect_char_X={5'b00000,5'b10001,5'b10001,5'b01010,5'b00100,5'b01010,5'b10001,5'b10001};
  localparam logic [39:0] vect_char_space={5'b00000,5'b00000,5'b00000,5'b00000,5'b00000,5'b00000,5'b00000,5'b00000};
  localparam logic [39:0] vect_char_D={5'b00000,5'b00111,5'b01001,5'b10001,5'b10001,5'b10001,5'b01001,5'b00111};
  localparam logic [39:0] vect_char_H={5'b00000,5'b10001,5'b10001,5'b10001,5'b11111,5'b10001,5'b10001,5'b10001};

  localparam logic [39:0] vect_op_AND  ={5'b00000,5'b10110,5'b01001,5'b10101,5'b00010,5'b00101,5'b01001,5'b00110};
  localparam logic [39:0] vect_op_mult ={5'b00000,5'b00100,5'b10101,5'b01110,5'b10101,5'b00100,5'b00000,5'b00000};
  localparam logic [39:0] vect_op_suma ={5'b00000,5'b00100,5'b00100,5'b11111,5'b00100,5'b00100,5'b00000,5'b00000};
  localparam logic [39:0] vect_op_OR   ={5'b00100,5'b00100,5'b00100,5'b00100,5'b00100,5'b00100,5'b00100,5'b00100};
  localparam logic [39:0] vect_op_resta={5'b00000,5'b00000,5'b00000,5'b11111,5'b00000,5'b00000,5'b00000,5'b00000};

  localparam logic [39:0] vect_num_0={5'b00000,5'b01110,5'b10001,5'b10011,5'b10101,5'b11001,5'b10001,5'b01110};
  localparam logic [39:0] vect_num_1={5'b00000,5'b01110,5'b00100,5'b00100,5'b00100,5'b00100,5'b00110,5'b00100};
  localparam logic [39:0] vect_num_2={5'b00000,5'b11111,5'b00010,5'b00100,5'b01000,5'b10000,5'b10001,5'b01110};
  localparam logic [39:0] vect_num_3={5'b00000,5'b01110,5'b10001,5'b10000,5'b01000,5'b00100,5'b01000,5'b11111};
  localparam logic [39:0] vect_num_4={5'b00000,5'b01000,5'b01000,5'b11111,5'b01001,5'b01010,5'b01100,5'b01000};
  localparam logic [39:0] vect_num_5={5'b00000,5'b0110,5'b10001,5'b10000,5'b10000,5'b01111,5'b00010,5'b11111};
  localparam logic [39:0] vect_num_6={5'b00000,5'b01110,5'b10001,5'b10001,5'b01111,5'b00001,5'b00010,5'b01100};
  localparam logic [39:0] vect_num_7={5'b00000,5'b00010,5'b00010,5'b00010,5'b00100,5'b01000,5'b10000,5'b11111};
  localparam logic [39:0] vect_num_8={5'b00000,5'b01110,5'b10001,5'b10001,5'b01110,5'b10001,5'b10001,5'b01110};
  localparam logic [39:0] vect_num_9={5'b00000,5'b00110,5'b01000,5'b10000,5'b11110,5'b10001,5'b10001,5'b01110};
  localparam logic [39:0] vect_num_p={5'b00000,5'b00110,5'b00110,5'b00000,5'b00000,5'b00000,5'b00000,5'b00000};

  function automatic logic [39:0] expected_vec (input logic [7:0] s);
    unique case (s)
      8'd0  : expected_vec = vect_num_0;
      8'd1  : expected_vec = vect_num_1;
      8'd2  : expected_vec = vect_num_2;
      8'd3  : expected_vec = vect_num_3;
      8'd4  : expected_vec = vect_num_4;
      8'd5  : expected_vec = vect_num_5;
      8'd6  : expected_vec = vect_num_6;
      8'd7  : expected_vec = vect_num_7;
      8'd8  : expected_vec = vect_num_8;
      8'd9  : expected_vec = vect_num_9;
      8'd46 : expected_vec = vect_num_p;          // '.'
      8'd43 : expected_vec = vect_op_suma;        // '+'
      8'd42 : expected_vec = vect_op_mult;        // '*'
      8'd45 : expected_vec = vect_op_resta;       // '-'
      8'd124: expected_vec = vect_op_OR;          // '|'
      8'd38 : expected_vec = vect_op_AND;         // '&'
      8'd32 : expected_vec = vect_char_space;     // ' '
      8'd10 : expected_vec = vect_char_a;
      8'd11 : expected_vec = vect_char_b;
      8'd12 : expected_vec = vect_char_c;
      8'd13 : expected_vec = vect_char_d;
      8'd14 : expected_vec = vect_char_e;
      8'd15 : expected_vec = vect_char_f;
      8'd103: expected_vec = vect_char_g;
      8'd104: expected_vec = vect_char_h;
      8'd105: expected_vec = vect_char_i;
      8'd106: expected_vec = vect_char_j;
      8'd107: expected_vec = vect_char_k;
      8'd108: expected_vec = vect_char_l;
      8'd109: expected_vec = vect_char_m;
      8'd110: expected_vec = vect_char_n;
      8'd111: expected_vec = vect_char_o;
      8'd112: expected_vec = vect_char_p;
      8'd113: expected_vec = vect_char_q;
      8'd114: expected_vec = vect_char_r;
      8'd115: expected_vec = vect_char_s;
      8'd116: expected_vec = vect_char_t;
      8'd117: expected_vec = vect_char_u;
      8'd118: expected_vec = vect_char_v;
      8'd119: expected_vec = vect_char_w;
      8'd120: expected_vec = vect_char_x;
      8'd121: expected_vec = vect_char_y;
      8'd122: expected_vec = vect_char_z;
      8'd201: expected_vec = vect_char_E;
      8'd199: expected_vec = vect_char_C;
      8'd220: expected_vec = vect_char_X;
      8'd200: expected_vec = vect_char_D;
      8'd204: expected_vec = vect_char_H;
      default: expected_vec = vect_num_p;
    endcase
  endfunction

  // Decode correctness
  property p_decode_ok;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(select) |-> (vec_char == expected_vec(select));
  endproperty
  assert property (p_decode_ok) else $error("characters: vec_char mismatch for select=%0d (0x%0h)", select, select);

  // No X/Z on output when input is known
  property p_no_x_out;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(select) |-> !$isunknown(vec_char);
  endproperty
  assert property (p_no_x_out) else $error("characters: vec_char has X/Z for known select=%0d", select);

  // Stability: if select stable, vec_char stable
  property p_stable;
    @(posedge clk) disable iff (!rst_n)
      $stable(select) |-> $stable(vec_char);
  endproperty
  assert property (p_stable) else $error("characters: vec_char changed without select change");

  // Functional coverage of all decoded values (one-liners for each key code)
  cover property (@(posedge clk) select==8'd0);
  cover property (@(posedge clk) select==8'd1);
  cover property (@(posedge clk) select==8'd2);
  cover property (@(posedge clk) select==8'd3);
  cover property (@(posedge clk) select==8'd4);
  cover property (@(posedge clk) select==8'd5);
  cover property (@(posedge clk) select==8'd6);
  cover property (@(posedge clk) select==8'd7);
  cover property (@(posedge clk) select==8'd8);
  cover property (@(posedge clk) select==8'd9);
  cover property (@(posedge clk) select==8'd46);
  cover property (@(posedge clk) select==8'd43);
  cover property (@(posedge clk) select==8'd42);
  cover property (@(posedge clk) select==8'd45);
  cover property (@(posedge clk) select==8'd124);
  cover property (@(posedge clk) select==8'd38);
  cover property (@(posedge clk) select==8'd32);
  cover property (@(posedge clk) select==8'd10);
  cover property (@(posedge clk) select==8'd11);
  cover property (@(posedge clk) select==8'd12);
  cover property (@(posedge clk) select==8'd13);
  cover property (@(posedge clk) select==8'd14);
  cover property (@(posedge clk) select==8'd15);
  cover property (@(posedge clk) select==8'd103);
  cover property (@(posedge clk) select==8'd104);
  cover property (@(posedge clk) select==8'd105);
  cover property (@(posedge clk) select==8'd106);
  cover property (@(posedge clk) select==8'd107);
  cover property (@(posedge clk) select==8'd108);
  cover property (@(posedge clk) select==8'd109);
  cover property (@(posedge clk) select==8'd110);
  cover property (@(posedge clk) select==8'd111);
  cover property (@(posedge clk) select==8'd112);
  cover property (@(posedge clk) select==8'd113);
  cover property (@(posedge clk) select==8'd114);
  cover property (@(posedge clk) select==8'd115);
  cover property (@(posedge clk) select==8'd116);
  cover property (@(posedge clk) select==8'd117);
  cover property (@(posedge clk) select==8'd118);
  cover property (@(posedge clk) select==8'd119);
  cover property (@(posedge clk) select==8'd120);
  cover property (@(posedge clk) select==8'd121);
  cover property (@(posedge clk) select==8'd122);
  cover property (@(posedge clk) select==8'd201);
  cover property (@(posedge clk) select==8'd199);
  cover property (@(posedge clk) select==8'd220);
  cover property (@(posedge clk) select==8'd200);
  cover property (@(posedge clk) select==8'd204);
  // Default path coverage (choose a value not in the decoded set)
  cover property (@(posedge clk) !(select inside {
      8'd0,8'd1,8'd2,8'd3,8'd4,8'd5,8'd6,8'd7,8'd8,8'd9,
      8'd46,8'd43,8'd42,8'd45,8'd124,8'd38,8'd32,
      8'd10,8'd11,8'd12,8'd13,8'd14,8'd15,
      8'd103,8'd104,8'd105,8'd106,8'd107,8'd108,8'd109,8'd110,8'd111,8'd112,
      8'd113,8'd114,8'd115,8'd116,8'd117,8'd118,8'd119,8'd120,8'd121,8'd122,
      8'd201,8'd199,8'd220,8'd200,8'd204
  }));

endmodule

// Example bind (provide a clock/reset from your env):
// bind characters characters_sva u_characters_sva ( .clk(tb_clk), .rst_n(tb_rst_n), .select(select), .vec_char(vec_char) );