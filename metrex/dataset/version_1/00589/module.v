module timer_module
(
  input   clk,            // clock
  input   wr,            // write enable
  input   reset,           // reset
  input   tlo,          // timer low byte select
  input   thi,           // timer high byte select
  input   tcr,          // timer control register
  input   [7:0] data_in,      // bus data in
  input   count_en,        // enable or disable the timer count
  input   [15:0] load_val,    // initial value of the timer counter
  output  [7:0] data_out,      // bus data out
  output  tmra_ovf,        // timer A underflow
  output  spmode,          // serial port mode
  output  irq,            // interrupt out
  output  [15:0] count_val    // current count value
);

reg    [15:0] tmr;        // timer
reg    [7:0] tmlh;        // timer latch high byte
reg    [7:0] tmll;        // timer latch low byte
reg    [6:0] tmcr;        // timer control register
reg    forceload;        // force load strobe
wire   oneshot;        // oneshot mode
wire   start;          // timer start (enable)
reg    thi_load;          // load tmr after writing thi in one-shot mode
wire   reload;          // reload timer counter
wire   zero;          // timer counter is zero
wire   underflow;        // timer is going to underflow
wire   count;          // count enable signal

// count enable signal
assign count = count_en;

// writing timer control register
always @(posedge clk)
  if (reset)  // synchronous reset
    tmcr[6:0] <= 7'd0;
  else if (tcr && wr)  // load control register, bit 4(strobe) is always 0
    tmcr[6:0] <= {data_in[6:5],1'b0,data_in[3:0]};
  else if (thi_load && oneshot)  // start timer if thi is written in one-shot mode
    tmcr[0] <= 1'd1;
  else if (underflow && oneshot) // stop timer in one-shot mode
    tmcr[0] <= 1'd0;

always @(posedge clk)
  forceload <= tcr & wr & data_in[4];  // force load strobe

assign oneshot = tmcr[3];    // oneshot alias
assign start = tmcr[0];      // start alias
assign spmode = tmcr[6];    // serial port mode (0-input, 1-output)

// timer A latches for high and low byte
always @(posedge clk)
  if (reset)
    tmll[7:0] <= 8'b1111_1111;
  else if (tlo && wr)
    tmll[7:0] <= data_in[7:0];

always @(posedge clk)
  if (reset)
    tmlh[7:0] <= 8'b1111_1111;
  else if (thi && wr)
    tmlh[7:0] <= data_in[7:0];

// thi is written in one-shot mode so tmr must be reloaded
always @(posedge clk)
  thi_load <= thi & wr & (~start | oneshot);

// timer counter reload signal
assign reload = thi_load | forceload | underflow;

// timer counter
always @(posedge clk)
  if (reset)
    tmr[15:0] <= 16'hFF_FF;
  else if (reload)
    tmr[15:0] <= load_val[15:0];
  else if (start && count)
    tmr[15:0] <= tmr[15:0] - 16'd1;

// timer counter equals zero
assign zero = ~|tmr;

// timer counter is going to underflow
assign underflow = zero & start & count;

// Timer A underflow signal for Timer B
assign tmra_ovf = underflow;

// timer underflow interrupt request
assign irq = underflow;

// data output
assign data_out[7:0] = ({8{~wr&tlo}} & tmr[7:0])
          | ({8{~wr&thi}} & tmr[15:8])
          | ({8{~wr&tcr}} & {1'b0,tmcr[6:0]});

// current count value
assign count_val = tmr;

endmodule