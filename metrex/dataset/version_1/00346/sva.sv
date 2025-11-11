// SVA for double_divider
// Bind this checker to the DUT. Focused, high-signal-coverage, concise assertions and covers.

bind double_divider dd_sva();

module dd_sva;

  // Pull internal signals by name via bind scope
  // Clock, reset
  wire        clk, rst;

  // Handshakes and IO
  wire [63:0] input_a, input_b;
  wire        input_a_stb, input_b_stb, output_z_ack;
  wire        input_a_ack, input_b_ack;
  wire [63:0] output_z;
  wire        output_z_stb;

  // Internals
  wire        s_input_a_ack, s_input_b_ack, s_output_z_stb;
  wire [63:0] s_output_z;
  wire [3:0]  state;
  wire [63:0] a, b, z;
  wire [52:0] a_m, b_m, z_m;
  wire [12:0] a_e, b_e, z_e;
  wire        a_s, b_s, z_s;
  wire        guard, round_bit, sticky;
  wire [108:0] quotient, divisor, dividend, remainder;
  wire [6:0]  count;

  // named constants (copy from DUT)
  localparam get_a         = 4'd0,
             get_b         = 4'd1,
             unpack        = 4'd2,
             special_cases = 4'd3,
             normalise_a   = 4'd4,
             normalise_b   = 4'd5,
             divide_0      = 4'd6,
             divide_1      = 4'd7,
             divide_2      = 4'd8,
             divide_3      = 4'd9,
             normalise_1   = 4'd10,
             normalise_2   = 4'd11,
             round         = 4'd12,
             pack          = 4'd13,
             put_z         = 4'd14;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Sanity: outputs mirror regs, acks mirror regs, state in-range, no X
  assert property (output_z       == s_output_z);
  assert property (output_z_stb   == s_output_z_stb);
  assert property (input_a_ack    == s_input_a_ack);
  assert property (input_b_ack    == s_input_b_ack);
  assert property (state inside {get_a,get_b,unpack,special_cases,normalise_a,normalise_b,
                                 divide_0,divide_1,divide_2,divide_3,normalise_1,normalise_2,round,pack,put_z});
  assert property (!$isunknown({state,s_input_a_ack,s_input_b_ack,s_output_z_stb}));

  // Reset behavior (synchronous)
  assert property (@(posedge clk) rst |-> (state==get_a && !s_input_a_ack && !s_input_b_ack && !s_output_z_stb));

  // Handshake discipline: which ack/stb are allowed in which state
  assert property (state==get_a |-> s_input_a_ack);
  assert property (state!=get_a |-> !s_input_a_ack);
  assert property (state==get_b |-> s_input_b_ack);
  assert property (state!=get_b |-> !s_input_b_ack);
  assert property (state==put_z |-> s_output_z_stb);
  assert property (state!=put_z |-> !s_output_z_stb);

  // Mutual exclusion of interface intents
  assert property (!(s_input_a_ack && (s_input_b_ack || s_output_z_stb)));
  assert property (!(s_input_b_ack && s_output_z_stb));

  // Legal state transitions
  assert property (state==get_a        |=> state inside {get_a,get_b});
  assert property (state==get_b        |=> state inside {get_b,unpack});
  assert property (state==unpack       |=> state==special_cases);
  assert property (state==special_cases|=> state inside {normalise_a,put_z});
  assert property (state==normalise_a  |=> state inside {normalise_a,normalise_b});
  assert property (state==normalise_b  |=> state inside {normalise_b,divide_0});
  assert property (state==divide_0     |=> state==divide_1);
  assert property (state==divide_1     |=> state==divide_2);
  assert property (state==divide_2     |=> state inside {divide_1,divide_3});
  assert property (state==divide_3     |=> state==normalise_1);
  assert property (state==normalise_1  |=> state inside {normalise_1,normalise_2});
  assert property (state==normalise_2  |=> state inside {normalise_2,round});
  assert property (state==round        |=> state==pack);
  assert property (state==pack         |=> state==put_z);
  assert property (state==put_z        |=> state inside {put_z,get_a});

  // Input handshakes
  assert property (state==get_a && s_input_a_ack && input_a_stb |=> state==get_b && !s_input_a_ack && a==$past(input_a));
  assert property (state==get_a && !(s_input_a_ack && input_a_stb) |=> state==get_a && s_input_a_ack);

  assert property (state==get_b && s_input_b_ack && input_b_stb |=> state==unpack && !s_input_b_ack && b==$past(input_b));
  assert property (state==get_b && !(s_input_b_ack && input_b_stb) |=> state==get_b && s_input_b_ack);

  // Unpack loads from a,b
  assert property ($past(state)==unpack |-> state==special_cases
                   && a_m==$past(a[51:0])
                   && b_m==$past(b[51:0])
                   && a_s==$past(a[63])
                   && b_s==$past(b[63])
                   && a_e==$signed({2'b00,$past(a[62:52])}) - 13'sd1023
                   && b_e==$signed({2'b00,$past(b[62:52])}) - 13'sd1023);

  // Divide_0 initialization
  assert property ($past(state)==divide_0 |-> state==divide_1
                   && z_s==$past(a_s ^ b_s)
                   && z_e==$signed($past(a_e)) - $signed($past(b_e))
                   && quotient==0 && remainder==0 && count==0
                   && dividend==($past(a_m) << 56)
                   && divisor==$past(b_m));

  // Divide_3 -> normalise_1: export QRSS
  assert property ($past(state)==divide_3 |-> state==normalise_1
                   && z_m==$past(quotient[55:3])
                   && guard==$past(quotient[2])
                   && round_bit==$past(quotient[1])
                   && sticky==($past(quotient[0]) | ($past(remainder)!=0)));

  // Normalise_1 step behavior
  assert property (state==normalise_1 && (z_m[52]==1'b0) && ($signed(z_e) > -13'sd1022)
                   |=> state==normalise_1
                       && z_e==$past(z_e)-13'sd1
                       && z_m==={$past(z_m[51:0]), $past(guard)}
                       && guard==$past(round_bit)
                       && round_bit==1'b0);

  // Normalise_2 step behavior
  assert property (state==normalise_2 && ($signed(z_e) < -13'sd1022)
                   |=> state==normalise_2
                       && z_e==$past(z_e)+13'sd1
                       && z_m==={1'b0, $past(z_m[52:1])}
                       && guard==$past(z_m[0])
                       && round_bit==$past(guard)
                       && sticky==($past(sticky) | $past(round_bit)));

  // Rounding behavior
  assert property (state==round && guard && (round_bit || sticky || z_m[0])
                   |=> z_m==$past(z_m)+53'd1
                       && ( ($past(z_m)==53'h0000_0000_0000_0000_0000_0ffffff) -> (z_e==$past(z_e)+13'sd1)) );
  assert property (state==round && !(guard && (round_bit || sticky || z_m[0])) |=> z_m==$past(z_m));

  // Pack -> put_z: final formatting
  // Overflow to Inf
  assert property ($past(state)==pack && ($signed($past(z_e)) > 13'sd1023)
                   |-> state==put_z
                       && s_output_z_stb && s_output_z[51:0]==0 && s_output_z[62:52]==11'd2047 && s_output_z[63]==$past(z_s));
  // Subnormal exponent case
  assert property ($past(state)==pack && ($signed($past(z_e)) == -13'sd1022) && ($past(z_m[52])==1'b0)
                   |-> state==put_z
                       && s_output_z_stb && s_output_z[62:52]==11'd0);
  // Normal finite case
  assert property ($past(state)==pack && !($signed($past(z_e)) > 13'sd1023)
                                   && !(($signed($past(z_e)) == -13'sd1022) && ($past(z_m[52])==1'b0))
                   |-> state==put_z
                       && s_output_z_stb
                       && s_output_z[51:0]==$past(z_m[51:0])
                       && s_output_z[62:52]==($past(z_e[10:0]) + 11'd1023)
                       && s_output_z[63]==$past(z_s));

  // put_z persistence and handshake
  assert property (state==put_z && s_output_z_stb && !output_z_ack |=> state==put_z && s_output_z_stb && $stable(s_output_z));
  assert property (state==put_z && s_output_z_stb && output_z_ack |=> state==get_a && !s_output_z_stb);

  // Functional coverage

  // Full transaction with handshakes
  cover property (state==get_a ##1 (state==get_a && s_input_a_ack && input_a_stb)
                  ##1 state==get_b ##1 (state==get_b && s_input_b_ack && input_b_stb)
                  ##[1:400] state==put_z ##1 (state==put_z && s_output_z_stb && output_z_ack)
                  ##1 state==get_a);

  // Special-cases coverage (NaN, Inf, Zero, Div-by-zero)
  cover property (state==special_cases && (a_e==13'd1024) && (a_m!=0)); // a is NaN
  cover property (state==special_cases && (b_e==13'd1024) && (b_m!=0)); // b is NaN
  cover property (state==special_cases && (a_e==13'd1024) && (b_e==13'd1024)); // inf/inf
  cover property (state==special_cases && ($signed(b_e)==-13'sd1023) && (b_m==0)); // divide by zero
  cover property (state==special_cases && ($signed(a_e)==-13'sd1023) && (a_m==0)); // zero numerator

  // Normal datapath with rounding increment
  cover property (state==round && guard && (round_bit || sticky || z_m[0]));

  // Overflow and subnormal pack
  cover property ($past(state)==pack && ($signed($past(z_e)) > 13'sd1023));
  cover property ($past(state)==pack && ($signed($past(z_e)) == -13'sd1022) && ($past(z_m[52])==0));

endmodule