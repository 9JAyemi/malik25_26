// SVA for mux_parity
// Includes black-box functional checks and concise white-box structural checks.
// Bind these checkers to the DUT instance(s).

// Black-box functional checker (ports only)
module mux_parity_sva_bb (
  input logic [2:0] sel,
  input logic [3:0] data0,
  input logic [3:0] data1,
  input logic [3:0] data2,
  input logic [3:0] data3,
  input logic [3:0] data4,
  input logic [3:0] data5,
  input logic [3:0] out,
  input logic       parity
);
  default clocking cb @(*); endclocking

  // Functional mapping of out
  assert property ( out ==
                    ((sel==3'd0) ? data0 :
                     (sel==3'd1) ? data1 :
                     (sel==3'd2) ? data2 :
                     (sel==3'd3) ? data3 :
                     (sel==3'd4) ? data4 :
                     (sel==3'd5) ? data5 :
                                    4'b0) );

  // Parity equals XOR of out bits
  assert property ( parity == (out[0]^out[1]^out[2]^out[3]) );

  // Coverage: each select hit with expected effect, plus illegal selects driving zero
  cover property ( (sel==3'd0) && (out==data0) );
  cover property ( (sel==3'd1) && (out==data1) );
  cover property ( (sel==3'd2) && (out==data2) );
  cover property ( (sel==3'd3) && (out==data3) );
  cover property ( (sel==3'd4) && (out==data4) );
  cover property ( (sel==3'd5) && (out==data5) );
  cover property ( (sel inside {3'd6,3'd7}) && (out==4'b0) );

  // Parity value coverage
  cover property ( parity==1'b0 );
  cover property ( parity==1'b1 );
endmodule

// White-box structural checker (uses DUT internals)
module mux_parity_sva_wb (
  input logic [2:0] sel,
  input logic [3:0] data0,
  input logic [3:0] data1,
  input logic [3:0] data2,
  input logic [3:0] data3,
  input logic [3:0] data4,
  input logic [3:0] data5,
  input logic [3:0] out,
  input logic       parity,

  // Internal nets from DUT
  input logic [3:0] mux_out [0:5],
  input logic [2:0] sel_dec [0:7]
);
  default clocking cb @(*); endclocking

  // Decoder bits must be zero-extended 1-bit values (only LSB may be 1)
  assert property ( sel_dec[0][2:1]==2'b00 );
  assert property ( sel_dec[1][2:1]==2'b00 );
  assert property ( sel_dec[2][2:1]==2'b00 );
  assert property ( sel_dec[3][2:1]==2'b00 );
  assert property ( sel_dec[4][2:1]==2'b00 );
  assert property ( sel_dec[5][2:1]==2'b00 );
  assert property ( sel_dec[6]      ==3'b000 );
  assert property ( sel_dec[7]      ==3'b000 );

  // Decoder correctness (LSB mirrors comparisons)
  assert property ( sel_dec[0][0] == (sel==3'd0) );
  assert property ( sel_dec[1][0] == (sel==3'd1) );
  assert property ( sel_dec[2][0] == (sel==3'd2) );
  assert property ( sel_dec[3][0] == (sel==3'd3) );
  assert property ( sel_dec[4][0] == (sel==3'd4) );
  assert property ( sel_dec[5][0] == (sel==3'd5) );
  assert property ( sel_dec[6][0] == 1'b0 );
  assert property ( sel_dec[7][0] == 1'b0 );

  // One-hot-0 decode across all 8 entries (at most one asserted)
  assert property ( $onehot0({ sel_dec[7][0], sel_dec[6][0], sel_dec[5][0], sel_dec[4][0],
                               sel_dec[3][0], sel_dec[2][0], sel_dec[1][0], sel_dec[0][0] }) );

  // Gating correctness for each leg
  assert property ( mux_out[0] == (sel_dec[0][0] ? data0 : 4'b0) );
  assert property ( mux_out[1] == (sel_dec[1][0] ? data1 : 4'b0) );
  assert property ( mux_out[2] == (sel_dec[2][0] ? data2 : 4'b0) );
  assert property ( mux_out[3] == (sel_dec[3][0] ? data3 : 4'b0) );
  assert property ( mux_out[4] == (sel_dec[4][0] ? data4 : 4'b0) );
  assert property ( mux_out[5] == (sel_dec[5][0] ? data5 : 4'b0) );

  // OR tree correctness
  assert property ( out == (mux_out[0] | mux_out[1] | mux_out[2] |
                            mux_out[3] | mux_out[4] | mux_out[5]) );

  // Coverage: each decode bit asserted
  cover property ( sel_dec[0][0] );
  cover property ( sel_dec[1][0] );
  cover property ( sel_dec[2][0] );
  cover property ( sel_dec[3][0] );
  cover property ( sel_dec[4][0] );
  cover property ( sel_dec[5][0] );
endmodule

// Bind to DUT
bind mux_parity mux_parity_sva_bb bb (.*);
bind mux_parity mux_parity_sva_wb wb (.*);