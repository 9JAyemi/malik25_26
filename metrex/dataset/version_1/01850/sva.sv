// SVA for SDCard. Bind this file to the DUT.
// Focused, concise checks with essential cover.

module SDCard_sva (
  input logic         clk_i,
  input logic         cpuclk_n_i,
  input logic         reset_n_i,
  input logic         cs_i,
  input logic         adr_i,
  input logic         rw_n_i,
  input logic  [7:0]  dat_i,
  input logic  [7:0]  dat_o,
  input logic         irq_n_o,
  input logic         act_led_n_o,
  input logic         card_detect_n_i,
  input logic         wp_locked_i,
  input logic         miso_i,
  input logic         irq_reset_n,
  input logic         halt_o,
  input logic         sclk_o,
  input logic         mosi_o,
  input logic         spi_ss_n_o,
  // internal regs
  input logic         en_spi,
  input logic  [2:0]  state,
  input logic  [3:0]  bcnt,
  input logic         wffull,
  input logic  [1:0]  wffull_buf,
  input logic  [7:0]  rreg1,
  input logic  [7:0]  buffer1,
  input logic         wffull_reset,
  input logic  [2:0]  cd_buff0,
  input logic         irq_n,
  input logic         en_irq,
  input logic         halt_buf0,
  input logic         halt_buf1,
  input logic  [1:0]  halt_state
);

  // State aliases
  localparam logic [2:0] ST_IDLE   = 3'b001;
  localparam logic [2:0] ST_DRIVE  = 3'b010;
  localparam logic [2:0] ST_SAMPLE = 3'b100;

  // Simple equalities
  assert property (@(posedge clk_i)  act_led_n_o == state[0]);
  assert property (@(posedge clk_i)  irq_n_o     == irq_n);
  assert property (@(negedge cpuclk_n_i) irq_reset_n == (reset_n_i && en_spi && en_irq));

  // dat_o mapping (sample on both domains)
  assert property (@(posedge clk_i)        !adr_i |-> dat_o == {~irq_n,5'b0,wp_locked_i,~card_detect_n_i});
  assert property (@(negedge cpuclk_n_i)   !adr_i |-> dat_o == {~irq_n,5'b0,wp_locked_i,~card_detect_n_i});
  assert property (@(posedge clk_i)         adr_i |-> dat_o == rreg1);
  assert property (@(negedge cpuclk_n_i)    adr_i |-> dat_o == rreg1);

  // CPU-domain reset effects
  assert property (@(negedge cpuclk_n_i) !reset_n_i |-> (spi_ss_n_o==1 && en_irq==0 && en_spi==0 && buffer1==8'hFF));
  assert property (@(negedge cpuclk_n_i) !reset_n_i |-> (halt_o==1'b0 && halt_state==2'b00));

  // Control writes (CPU domain)
  assert property (@(negedge cpuclk_n_i) (reset_n_i && {cs_i,rw_n_i,adr_i}==3'b100)
                   |=> (en_spi==dat_i[7] && en_irq==dat_i[6] && spi_ss_n_o == (!dat_i[0] | !dat_i[7])));
  assert property (@(negedge cpuclk_n_i) (reset_n_i && {cs_i,rw_n_i,adr_i}==3'b101)
                   |=> buffer1==dat_i);
  assert property (@(negedge cpuclk_n_i) (reset_n_i && {cs_i,rw_n_i,adr_i}==3'b111)
                   |=> buffer1==8'hFF);

  // wffull async clear
  assert property (@(posedge wffull_reset) wffull==1'b0);

  // SPI engine forced idle when disabled
  assert property (@(posedge clk_i) !reset_n_i or !en_spi
                   |-> (state==ST_IDLE && bcnt==4'h0 && sclk_o==1'b0 && wffull_reset==1'b1 && wffull_buf==2'b00 && rreg1==8'h00));

  // wffull_buf shifter (when running)
  assert property (@(posedge clk_i) reset_n_i && en_spi && $past(en_spi)
                   |-> wffull_buf == { $past(wffull_buf[0]), $past(wffull) });

  // sclk relation to state
  assert property (@(posedge clk_i) sclk_o == (state==ST_SAMPLE));

  // State: IDLE -> DRIVE on data ready
  assert property (@(posedge clk_i) reset_n_i && en_spi && state==ST_IDLE && wffull_buf[1]
                   |=> (state==ST_DRIVE && bcnt==4'h0 && rreg1==$past(buffer1) && !wffull_reset && sclk_o==1'b0));

  // DRIVE behavior (bcnt[3]==0): next SAMPLE with correct MOSI, wffull_reset asserted
  assert property (@(posedge clk_i) reset_n_i && en_spi && state==ST_DRIVE && !bcnt[3]
                   |=> (state==ST_SAMPLE && wffull_reset && sclk_o==1'b1 && mosi_o==$past(rreg1[7])));

  // DRIVE done (bcnt[3]==1): go IDLE, deassert wffull_reset, mosi_o=1
  assert property (@(posedge clk_i) reset_n_i && en_spi && state==ST_DRIVE && bcnt[3]
                   |=> (state==ST_IDLE && !wffull_reset && mosi_o==1'b1));

  // SAMPLE -> DRIVE, shift-in and count increment
  assert property (@(posedge clk_i) reset_n_i && en_spi && state==ST_SAMPLE
                   |=> (state==ST_DRIVE && sclk_o==1'b0
                        && bcnt == $past(bcnt)+4'h1
                        && rreg1 == { $past(rreg1)[6:0], $past(miso_i) }));

  // wffull_reset polarity in key states
  assert property (@(posedge clk_i) (state==ST_DRIVE) |-> wffull_reset);
  assert property (@(posedge clk_i) (en_spi && state==ST_IDLE) |-> !wffull_reset);

  // IRQ logic
  assert property (@(negedge cpuclk_n_i) !irq_reset_n |-> (irq_n==1'b1 && cd_buff0==3'b000));
  assert property (@(negedge cpuclk_n_i) $fell(irq_n) |-> ($past(irq_reset_n) && $past(cd_buff0)==3'b100));

  // Halt handshake FSM
  assert property (@(negedge cpuclk_n_i) reset_n_i && halt_state==2'b00 && {cs_i,adr_i,en_spi}==3'b111
                   |=> (halt_o && halt_state==2'b01));
  assert property (@(negedge cpuclk_n_i) reset_n_i && halt_state==2'b01 && halt_buf1
                   |=> (halt_state==2'b10));
  assert property (@(negedge cpuclk_n_i) reset_n_i && halt_state==2'b10 && !halt_buf1
                   |=> (!halt_o && halt_state==2'b00));
  assert property (@(negedge cpuclk_n_i) halt_o |-> (halt_state inside {2'b01,2'b10}));

  // Halt domain sampling of state[0]
  assert property (@(negedge cpuclk_n_i) reset_n_i |-> (halt_buf0 == !$past(state[0]) && halt_buf1 == $past(halt_buf0)));

  // Coverage
  cover property (@(posedge clk_i) reset_n_i && en_spi && state==ST_IDLE && wffull_buf[1]
                  ##1 (state==ST_DRIVE ##1 state==ST_SAMPLE) [*8]
                  ##1 state==ST_DRIVE && bcnt[3]
                  ##1 state==ST_IDLE);

  cover property (@(negedge cpuclk_n_i) reset_n_i && !adr_i && en_irq && en_spi ##1 $fell(irq_n));
  cover property (@(negedge cpuclk_n_i) reset_n_i && halt_state==2'b00 && {cs_i,adr_i,en_spi}==3'b111
                  ##1 halt_state==2'b01 ##[1:5] halt_state==2'b10 ##[1:5] !halt_o && halt_state==2'b00);

  cover property (@(negedge cpuclk_n_i) reset_n_i && {cs_i,rw_n_i,adr_i}==3'b101);

endmodule

bind SDCard SDCard_sva sva (.*);