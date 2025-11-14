// SVA for konamicoder. Bind this file to the DUT.
module konamicoder_sva (
  input logic [3:0] state,
  input logic [6:0] digit_0,
  input logic [6:0] digit_1,
  input logic [6:0] digit_2,
  input logic [6:0] digit_3
);

  // Spec constants
  localparam logic [6:0] char_u = 7'b0111110;
  localparam logic [6:0] char_p = 7'b1110011;
  localparam logic [6:0] char_d = 7'b1011110;
  localparam logic [6:0] char_n = 7'b1010100;
  localparam logic [6:0] char_l = 7'b0111000;
  localparam logic [6:0] char_f = 7'b1110001;
  localparam logic [6:0] char_r = 7'b1010000;
  localparam logic [6:0] char_h = 7'b1110100;
  localparam logic [6:0] char_0 = 7'b0111111;
  localparam logic [6:0] char_1 = 7'b0000110;
  localparam logic [6:0] char_2 = 7'b1011011;
  localparam logic [6:0] char_9 = 7'b1101111;
  localparam logic [6:0] char__ = 7'b1000000; // underscore (char_)

  // Valid-state outputs must never be X/Z
  assert property (@(state) disable iff ($isunknown(state))
                   (state inside {[4'd0:4'd9]}) |-> !$isunknown({digit_0,digit_1,digit_2,digit_3}));

  // Output domain sanity: digits must be in allowed symbol sets
  assert property (@(state or digit_0) (digit_0 inside {char__,char_u,char_d,char_l,char_r,char_9,char_0}));
  assert property (@(state or digit_1) (digit_1 inside {char__,char_p,char_n,char_f,char_h,char_9,char_0}));
  assert property (@(state or digit_2) (digit_2 inside {char__,char_9,char_0}));
  assert property (@(state or digit_3) (digit_3 inside {char__,char_1,char_2,char_9,char_0}));

  // Functional mapping checks (concise per-state)
  assert property (@(state) disable iff ($isunknown(state))
                   (state==4'd0) |-> (digit_0==char__ && digit_1==char__ && digit_2==char__ && digit_3==char__));
  assert property (@(state) (state==4'd1) |-> (digit_0==char_u && digit_1==char_p && digit_2==char__ && digit_3==char_1));
  assert property (@(state) (state==4'd2) |-> (digit_0==char_u && digit_1==char_p && digit_2==char__ && digit_3==char_2));
  assert property (@(state) (state==4'd3) |-> (digit_0==char_d && digit_1==char_n && digit_2==char__ && digit_3==char_1));
  assert property (@(state) (state==4'd4) |-> (digit_0==char_d && digit_1==char_n && digit_2==char__ && digit_3==char_2));
  assert property (@(state) (state==4'd5) |-> (digit_0==char_l && digit_1==char_f && digit_2==char__ && digit_3==char_1));
  assert property (@(state) (state==4'd6) |-> (digit_0==char_r && digit_1==char_h && digit_2==char__ && digit_3==char_1));
  assert property (@(state) (state==4'd7) |-> (digit_0==char_l && digit_1==char_f && digit_2==char__ && digit_3==char_2));
  assert property (@(state) (state==4'd8) |-> (digit_0==char_r && digit_1==char_h && digit_2==char__ && digit_3==char_2));
  assert property (@(state) (state==4'd9) |-> (digit_0==char_9 && digit_1==char_9 && digit_2==char_9 && digit_3==char_9));
  // Default path (state 10..15)
  assert property (@(state) (!(state inside {[4'd0:4'd9]})) |-> (digit_0==char_0 && digit_1==char_0 && digit_2==char_0 && digit_3==char_0));

  // Output only changes when state changes (combinational stability)
  assert property (@(digit_0 or digit_1 or digit_2 or digit_3)
                   $changed({digit_0,digit_1,digit_2,digit_3}) |-> $changed(state));

  // Coverage: hit each state and the default path
  cover property (@(state) state==4'd0);
  cover property (@(state) state==4'd1);
  cover property (@(state) state==4'd2);
  cover property (@(state) state==4'd3);
  cover property (@(state) state==4'd4);
  cover property (@(state) state==4'd5);
  cover property (@(state) state==4'd6);
  cover property (@(state) state==4'd7);
  cover property (@(state) state==4'd8);
  cover property (@(state) state==4'd9);
  cover property (@(state) !(state inside {[4'd0:4'd9]}));

endmodule

// Bind to DUT
bind konamicoder konamicoder_sva i_konamicoder_sva (
  .state  (state),
  .digit_0(digit_0),
  .digit_1(digit_1),
  .digit_2(digit_2),
  .digit_3(digit_3)
);