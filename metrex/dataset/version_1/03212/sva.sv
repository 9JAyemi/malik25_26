// SVA for uart_rx. Bind this file to the DUT:
// bind uart_rx uart_rx_sva u_uart_rx_sva(.*);

module uart_rx_sva(
  input logic        clk,
  input logic        rst,
  input logic        RxD,
  input logic        uart_tick_16x,
  input logic [7:0]  RxD_data,
  input logic        ready,

  // internal DUT signals
  input logic [3:0]  state,
  input logic        clk_lock,
  input logic [3:0]  bit_spacing,
  input logic        capture,
  input logic        next_bit,
  input logic [1:0]  RxD_sync,
  input logic [1:0]  RxD_cnt,
  input logic        RxD_bit
);

  default clocking cb @(posedge clk); endclocking

  // State encodings (mirror DUT)
  localparam [3:0] IDLE=4'd0;
  localparam [3:0] BIT_0=4'd2, BIT_1=4'd3, BIT_2=4'd4, BIT_3=4'd5;
  localparam [3:0] BIT_4=4'd6, BIT_5=4'd7, BIT_6=4'd8, BIT_7=4'd9;
  localparam [3:0] STOP =4'd10;

  // Helpers
  sequence nb; uart_tick_16x && next_bit; endsequence

  // Basic correctness/legality
  assert property (disable iff (rst) state inside {IDLE,BIT_0,BIT_1,BIT_2,BIT_3,BIT_4,BIT_5,BIT_6,BIT_7,STOP});
  assert property (rst |=> state==IDLE);
  assert property (next_bit == (bit_spacing==4'hF));
  assert property (ready == (uart_tick_16x && next_bit && state==STOP));
  assert property (capture == (uart_tick_16x && next_bit && (state!=IDLE) && (state!=STOP)));

  // Hold when uart_tick_16x==0
  assert property (disable iff (rst) !uart_tick_16x |=> $stable(state));
  assert property (disable iff (rst) !uart_tick_16x |=> $stable(RxD_sync));
  assert property (disable iff (rst) !uart_tick_16x |=> $stable(RxD_cnt));
  assert property (disable iff (rst) !uart_tick_16x |=> $stable(RxD_bit));
  assert property (disable iff (rst) !uart_tick_16x |=> $stable(clk_lock));
  assert property (disable iff (rst) !uart_tick_16x |=> $stable(bit_spacing));

  // bit_spacing and next_bit timing vs clk_lock (NB semantics use past values)
  assert property (disable iff (rst) uart_tick_16x |=> bit_spacing == ($past(clk_lock) ? $past(bit_spacing)+4'h1 : 4'hE));

  // clk_lock update
  assert property (disable iff (rst) uart_tick_16x && !$past(clk_lock) |=> clk_lock == ~$past(RxD_bit));
  assert property (disable iff (rst) uart_tick_16x &&  $past(clk_lock) |=> clk_lock == (($past(state)==IDLE && $past(RxD_bit)) ? 1'b0 : 1'b1));

  // RxD synchronizer / filter behavior
  assert property (disable iff (rst)
    uart_tick_16x && ($past(RxD_sync[1])==1'b0) |=> RxD_cnt == ($past(RxD_cnt)==2'b11 ? 2'b11 : $past(RxD_cnt)+2'b01));
  assert property (disable iff (rst)
    uart_tick_16x && ($past(RxD_sync[1])==1'b1) |=> RxD_cnt == ($past(RxD_cnt)==2'b00 ? 2'b00 : $past(RxD_cnt)-2'b01));
  assert property (disable iff (rst)
    uart_tick_16x |=> RxD_bit == (($past(RxD_cnt)==2'b11) ? 1'b0 : (($past(RxD_cnt)==2'b00) ? 1'b1 : $past(RxD_bit))));
  assert property (disable iff (rst)
    $changed(RxD_bit) |-> (uart_tick_16x && ($past(RxD_cnt)==2'b11 || $past(RxD_cnt)==2'b00)));

  // State machine transitions (on tick only)
  assert property (disable iff (rst) uart_tick_16x && state==IDLE && !(next_bit && (RxD_bit==1'b0)) |=> state==IDLE);
  assert property (disable iff (rst) uart_tick_16x && state==IDLE &&  (next_bit && (RxD_bit==1'b0)) |=> state==BIT_0);

  assert property (disable iff (rst) uart_tick_16x && state==BIT_0 && !next_bit |=> state==BIT_0);
  assert property (disable iff (rst) uart_tick_16x && state==BIT_0 &&  next_bit |=> state==BIT_1);

  assert property (disable iff (rst) uart_tick_16x && state==BIT_1 && !next_bit |=> state==BIT_1);
  assert property (disable iff (rst) uart_tick_16x && state==BIT_1 &&  next_bit |=> state==BIT_2);

  assert property (disable iff (rst) uart_tick_16x && state==BIT_2 && !next_bit |=> state==BIT_2);
  assert property (disable iff (rst) uart_tick_16x && state==BIT_2 &&  next_bit |=> state==BIT_3);

  assert property (disable iff (rst) uart_tick_16x && state==BIT_3 && !next_bit |=> state==BIT_3);
  assert property (disable iff (rst) uart_tick_16x && state==BIT_3 &&  next_bit |=> state==BIT_4);

  assert property (disable iff (rst) uart_tick_16x && state==BIT_4 && !next_bit |=> state==BIT_4);
  assert property (disable iff (rst) uart_tick_16x && state==BIT_4 &&  next_bit |=> state==BIT_5);

  assert property (disable iff (rst) uart_tick_16x && state==BIT_5 && !next_bit |=> state==BIT_5);
  assert property (disable iff (rst) uart_tick_16x && state==BIT_5 &&  next_bit |=> state==BIT_6);

  assert property (disable iff (rst) uart_tick_16x && state==BIT_6 && !next_bit |=> state==BIT_6);
  assert property (disable iff (rst) uart_tick_16x && state==BIT_6 &&  next_bit |=> state==BIT_7);

  assert property (disable iff (rst) uart_tick_16x && state==BIT_7 && !next_bit |=> state==BIT_7);
  assert property (disable iff (rst) uart_tick_16x && state==BIT_7 &&  next_bit |=> state==STOP);

  assert property (disable iff (rst) uart_tick_16x && state==STOP  && !next_bit |=> state==STOP);
  assert property (disable iff (rst) uart_tick_16x && state==STOP  &&  next_bit |=> state==IDLE);

  // Data path
  assert property (disable iff (rst) capture |=> RxD_data == { $past(RxD_bit), $past(RxD_data[7:1]) });
  assert property (disable iff (rst) !capture |=> $stable(RxD_data));

  // Ready/capture exclusivity with states
  assert property (disable iff (rst) capture |-> (state inside {BIT_0,BIT_1,BIT_2,BIT_3,BIT_4,BIT_5,BIT_6,BIT_7}));
  assert property (disable iff (rst) ready   |-> (state==STOP));

  // Coverage
  cover property (ready);
  cover property (state inside {BIT_0,BIT_1,BIT_2,BIT_3,BIT_4,BIT_5,BIT_6,BIT_7,STOP});
  cover property (disable iff (rst)
    (state==IDLE && RxD_bit==1'b0 && nb) ##1 capture[*8] ##1 ready);
endmodule