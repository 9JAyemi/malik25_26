// SVA checker for StateUpdater
module StateUpdater_sva(
  input logic        clk,
  input logic        enable,
  input logic [6:0]  code,
  input logic [6:0]  addr,
  input logic [3:0]  state
);
  default clocking cb @(posedge clk); endclocking

  // make $past() safe from time 0
  logic past_valid;
  initial past_valid = 0;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // 4-bit mask produced by the RTL's (1 << addr) truncation semantics
  function automatic logic [3:0] mask4(input logic [6:0] a);
    mask4 = (32'h1 << a)[3:0];
  endfunction

  // decode with intended priority (top-to-bottom of case)
  wire p_all0 = enable && (code == 7'b0000000);
  wire p_all1 = enable && (code == 7'b1111111);

  wire p_tgl  = enable && !p_all0 && !p_all1 &&  code[0];
  wire p_set1 = enable && !p_all0 && !p_all1 && !code[0] &&  code[1];
  wire p_set0 = enable && !p_all0 && !p_all1 && !code[0] && !code[1] &&  code[2];
  wire p_inv  = enable && !p_all0 && !p_all1 && !code[0] && !code[1] && !code[2] &&  code[3];
  wire p_lsh  = enable && !p_all0 && !p_all1 && !code[0] && !code[1] && !code[2] && !code[3] &&  code[4];
  wire p_rsh  = enable && !p_all0 && !p_all1 && !code[0] && !code[1] && !code[2] && !code[3] && !code[4] && code[5];

  wire p_none = enable && !p_all0 && !p_all1 && (code[5:0] == 6'b0); // e.g., code==7'b1000000

  // state must hold when not enabled
  assert property ( !enable |=> $stable(state) );

  // exact code actions
  assert property ( p_all0 |=> state == 4'b0000 );
  assert property ( p_all1 |=> state == 4'b1111 );

  // prioritized pattern actions (using RTL's mask truncation semantics)
  assert property ( p_tgl  |=> state == ($past(state) ^  mask4($past(addr))) );
  assert property ( p_set1 |=> state == ($past(state) |  mask4($past(addr))) );
  assert property ( p_set0 |=> state == ($past(state) & ~mask4($past(addr))) );
  assert property ( p_inv  |=> state == ($past(state) ^  mask4($past(addr))) );
  assert property ( p_lsh  |=> state == { $past(state[2:0]), 1'b0 } );
  assert property ( p_rsh  |=> state == { 1'b0, $past(state[3:1]) } );

  // no matching pattern under enable => hold
  assert property ( p_none |=> state == $past(state) );

  // simple priority check example: if multiple bits set, earlier wins
  assert property ( enable && !p_all0 && !p_all1 && code[0] && code[1] |=> state == ($past(state) ^ mask4($past(addr))) );

  // Coverage: hit each operation and a hold
  cover property ( p_all0 ##1 state == 4'b0000 );
  cover property ( p_all1 ##1 state == 4'b1111 );
  cover property ( p_tgl  ##1 state == ($past(state) ^  mask4($past(addr))) );
  cover property ( p_set1 ##1 state == ($past(state) |  mask4($past(addr))) );
  cover property ( p_set0 ##1 state == ($past(state) & ~mask4($past(addr))) );
  cover property ( p_inv  ##1 state == ($past(state) ^  mask4($past(addr))) );
  cover property ( p_lsh  ##1 state == { $past(state[2:0]), 1'b0 } );
  cover property ( p_rsh  ##1 state == { 1'b0, $past(state[3:1]) } );
  cover property ( !enable ##1 $stable(state) );
  cover property ( p_none  ##1 $stable(state) );
endmodule

// Bind into the DUT
bind StateUpdater StateUpdater_sva sva_i(.clk(clk), .enable(enable), .code(code), .addr(addr), .state(state));