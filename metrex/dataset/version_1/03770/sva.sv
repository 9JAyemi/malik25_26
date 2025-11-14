// SVA for uart_tx
// Bind into DUT to access internals
module uart_tx_sva #(parameter int DBIT=8, SB_tck=16)
(
  input  logic        clk, reset,
  input  logic        tx_start, s_tck,
  input  logic [7:0]  din,
  input  logic        tx_done_tck,
  input  logic        tx,
  // internal DUT signals
  input  logic [1:0]  state,
  input  logic [3:0]  s,
  input  logic [2:0]  n,
  input  logic [7:0]  b,
  input  logic        tx_reg
);

  localparam logic [1:0] init_state=2'b00, start=2'b01, data=2'b10, stop=2'b11;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Parameter sanity vs counter widths
  initial begin
    assert (DBIT >= 1 && DBIT <= 8)
      else $error("DBIT out of supported [1..8]");
    assert (SB_tck >= 1 && SB_tck <= 16)
      else $error("SB_tck must be in [1..16] due to 4-bit s counter");
  end

  // Synchronous reset brings DUT to idle/mark
  assert property (@(posedge clk) reset |-> (state==init_state && s==0 && n==0 && b==0 && tx_reg==1'b1));

  // Basic invariants
  assert property (tx == tx_reg);
  assert property (state==init_state |-> tx==1'b1);
  assert property (state==start     |-> tx==1'b0);
  assert property (state==data      |-> tx==b[0]);
  assert property (state==stop      |-> tx==1'b1);
  assert property (! $isunknown({state,s,n,b,tx_reg,tx,tx_done_tck}));
  assert property (state inside {init_state,start,data,stop});

  // s only changes on s_tck in non-idle states
  assert property ($past(state inside {start,data,stop}) && !$past(s_tck) |-> s==$past(s));

  // Accept start in idle: load din, clear s, go to start
  assert property ($past(state)==init_state && $past(tx_start)
                   |-> state==start && s==0 && b==$past(din));

  // Start bit counting (16 ticks): increment s, then go to data with n=0
  assert property ($past(state)==start && $past(s_tck) && $past(s) < 15
                   |-> state==start && s==$past(s)+1);
  assert property ($past(state)==start && $past(s_tck) && $past(s)==15
                   |-> state==data && s==0 && n==0);

  // Data bit: stable within bit, shift/right and increment n on bit boundary
  assert property ($past(state)==data && (!$past(s_tck) || $past(s)!=15)
                   |-> state==data && b==$past(b) && n==$past(n) && tx==$past(tx));
  assert property ($past(state)==data && $past(s_tck) && $past(s)==15 && $past(n) < (DBIT-1)
                   |-> state==data && s==0 && n==$past(n)+1 && b==($past(b)>>1));
  assert property ($past(state)==data && $past(s_tck) && $past(s)==15 && $past(n)==(DBIT-1)
                   |-> state==stop && s==0 && b==($past(b)>>1));

  // Stop bit: count SB_tck ticks, then signal done and return to idle
  assert property ($past(state)==stop && $past(s_tck) && $past(s) < (SB_tck-1)
                   |-> state==stop && s==$past(s)+1 && !tx_done_tck);
  assert property ($past(state)==stop && $past(s_tck) && $past(s)==(SB_tck-1)
                   |-> state==init_state && tx_done_tck);

  // tx_done_tck is a single-cycle pulse and only from stop completion
  assert property (tx_done_tck
                   |-> $past(state)==stop && $past(s_tck) && $past(s)==(SB_tck-1) && state==init_state);
  assert property ($past(tx_done_tck) |-> !tx_done_tck);

  // Coverage
  cover property ($past(state)==init_state && $past(tx_start) ##[1:$] tx_done_tck); // full frame
  cover property (state==start && s==15 && s_tck ##1 state==data);                 // start->data
  cover property (state==data && tx==0);                                           // sending a 0 bit
  cover property (state==data && tx==1);                                           // sending a 1 bit
  cover property (state==stop && s==SB_tck-1 && s_tck ##1 tx_done_tck);            // stop complete
  cover property (tx_done_tck ##[1:5] (state==init_state && tx_start));            // back-to-back frames

endmodule

// Bind to DUT
bind uart_tx uart_tx_sva #(.DBIT(DBIT), .SB_tck(SB_tck)) uart_tx_sva_i
(
  .clk(clk),
  .reset(reset),
  .tx_start(tx_start),
  .s_tck(s_tck),
  .din(din),
  .tx_done_tck(tx_done_tck),
  .tx(tx),
  .state(state),
  .s(s),
  .n(n),
  .b(b),
  .tx_reg(tx_reg)
);