// SVA for identificador_teclas
module identificador_teclas_sva (
  input logic        clk,
  input logic        reset,
  input logic        rx_done_tick,
  input logic [7:0]  dout,
  input logic        gotten_code_flag,
  input logic        state_reg
);
  localparam logic WAIT = 1'b0;
  localparam logic GET  = 1'b1;
  localparam logic [7:0] BREAK = 8'hF0;

  // Reset behavior (async reset sampled on clk)
  assert property (@(posedge clk) reset |-> (state_reg==WAIT && !gotten_code_flag));

  // Knownness
  assert property (@(posedge clk) disable iff (reset) !$isunknown({state_reg, gotten_code_flag}));

  // WAIT state invariants and transitions
  assert property (@(posedge clk) disable iff (reset) (state_reg==WAIT) |-> !gotten_code_flag);
  assert property (@(posedge clk) disable iff (reset)
                   (state_reg==WAIT && rx_done_tick && dout==BREAK) |=> (state_reg==GET));
  assert property (@(posedge clk) disable iff (reset)
                   (state_reg==WAIT && rx_done_tick && dout!=BREAK) |=> (state_reg==WAIT));

  // GET state invariants, output, and transitions
  // Output equivalence
  assert property (@(posedge clk) disable iff (reset)
                   (gotten_code_flag == (state_reg==GET && rx_done_tick)));
  // Hold in GET when no tick
  assert property (@(posedge clk) disable iff (reset)
                   (state_reg==GET && !rx_done_tick) |=> (state_reg==GET));
  // On tick, return to WAIT
  assert property (@(posedge clk) disable iff (reset)
                   (state_reg==GET && rx_done_tick) |=> (state_reg==WAIT));

  // Legal transitions only
  assert property (@(posedge clk) disable iff (reset)
                   (state_reg==GET && $past(state_reg)!=GET) |-> $past(rx_done_tick && (dout==BREAK)));
  assert property (@(posedge clk) disable iff (reset)
                   (state_reg==WAIT && $past(state_reg)==GET) |-> $past(rx_done_tick));

  // Coverage
  cover property (@(posedge clk) disable iff (reset)
                  (state_reg==WAIT && rx_done_tick && dout==BREAK)
                  ##1 state_reg==GET [*1:$]
                  ##1 (state_reg==GET && rx_done_tick && gotten_code_flag)
                  ##1 state_reg==WAIT);

  cover property (@(posedge clk) disable iff (reset)
                  (state_reg==WAIT && rx_done_tick && dout!=BREAK) ##1 (state_reg==WAIT));

  cover property (@(posedge clk) disable iff (reset)
                  (state_reg==GET && !rx_done_tick)[*3]);
endmodule

// Bind into DUT (accessing internal state_reg)
bind identificador_teclas identificador_teclas_sva sva_i (
  .clk(clk),
  .reset(reset),
  .rx_done_tick(rx_done_tick),
  .dout(dout),
  .gotten_code_flag(gotten_code_flag),
  .state_reg(state_reg)
);