// SVA for up_down_counter
module up_down_counter_sva (
  input logic [2:0] D,
  input logic       UD,
  input logic       LD,
  input logic       CLK,
  input logic [2:0] Q
);
  default clocking cb @(posedge CLK); endclocking

  // Basic input sanity (no X where used)
  a_ld_known:              assert property ( !$isunknown(LD) );
  a_ud_known_when_count:   assert property ( !LD |-> !$isunknown(UD) );
  a_d_known_when_load:     assert property ( LD  |-> !$isunknown(D) );

  // Functional correctness
  a_load:       assert property ( LD |=> (Q == $past(D)) );

  a_count_down: assert property ( (!LD && UD)
                                  |=> ( ($past(Q)==3'd0) ? (Q==3'd7)
                                                         : (Q==$past(Q)-3'd1) ) );

  a_count_up:   assert property ( (!LD && !UD)
                                  |=> ( ($past(Q)==3'd7) ? (Q==3'd0)
                                                         : (Q==$past(Q)+3'd1) ) );

  // Q should be known after first sampled cycle
  logic seen_clk; initial seen_clk = 1'b0;
  always @(posedge CLK) seen_clk <= 1'b1;
  a_q_known: assert property ( seen_clk |-> !$isunknown(Q) );

  // Coverage
  c_load:        cover property ( LD );
  c_count_up:    cover property ( !LD && !UD );
  c_count_down:  cover property ( !LD && UD );

  // Wrap-around coverage
  c_up_wrap:     cover property ( (!LD && !UD && Q==3'd7) ##1 (!LD && !UD && Q==3'd0) );
  c_down_wrap:   cover property ( (!LD &&  UD && Q==3'd0) ##1 (!LD &&  UD && Q==3'd7) );

  // Direction switch coverage (down then up then down)
  c_dir_switch:  cover property ( (!LD && UD) ##1 (!LD && !UD) ##1 (!LD && UD) );

  // Load followed by counting
  c_load_then_cnt: cover property ( LD ##1 (!LD) );
endmodule

bind up_down_counter up_down_counter_sva sva_i (.D(D), .UD(UD), .LD(LD), .CLK(CLK), .Q(Q));