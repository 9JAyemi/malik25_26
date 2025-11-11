// SVA for gpio_wb — focused, high-quality checks and coverage
// Bindable checker using internal state_r (1’b0=IDLE, 1’b1=ACK)

module gpio_wb_sva #(parameter BASE_ADDR = 32'h00000400) (
  input  logic        clk_i,
  input  logic        rst_i,

  // WB bus
  input  logic [31:0] dat_i,
  input  logic [31:0] dat_o,
  input  logic [31:0] adr_i,
  input  logic        we_i,
  input  logic [3:0]  sel_i,
  input  logic        cyc_i,
  input  logic        stb_i,
  input  logic        ack_o,

  // GPIO
  input  logic [15:0] sw_bi,
  input  logic [15:0] gpio_bo,

  // internal
  input  logic        state_r
);

  localparam bit IDLE = 1'b0;
  localparam bit ACK  = 1'b1;

  logic read_s, write_s;
  assign read_s  = cyc_i & stb_i & ~we_i;
  assign write_s = cyc_i & stb_i &  we_i;

  // Reset values must hold while rst_i asserted (async reset)
  // Note: state_r is 0 on reset per RTL.
  assert property (@(posedge clk_i) rst_i |-> (state_r==IDLE && ack_o==1'b0 && dat_o==32'h0 && gpio_bo==16'h0));

  // State encoding invariant
  assert property (@(posedge clk_i) disable iff (rst_i)
                   (state_r inside {IDLE,ACK}));

  // From IDLE without request: stay IDLE and no ack next cycle
  assert property (@(posedge clk_i) disable iff (rst_i)
                   ($past(state_r==IDLE && !read_s && !write_s))
                   |-> (state_r==IDLE && ack_o==1'b0));

  // Accept WRITE in IDLE: ack now-and-next (observed as t and t+1 here), go to ACK,
  // correct GPIO update only when address matches
  assert property (@(posedge clk_i) disable iff (rst_i)
                   ($past(state_r==IDLE && write_s))
                   |-> (state_r==ACK && ack_o==1'b1 &&
                        (($past(adr_i)==BASE_ADDR) ? (gpio_bo==$past(dat_i[15:0]))
                                                    : (gpio_bo==$past(gpio_bo)))));

  assert property (@(posedge clk_i) disable iff (rst_i)
                   ($past(state_r==IDLE && write_s)) |=> ack_o==1'b1);

  // Accept READ in IDLE: data prepared, ack next cycle, enter ACK
  assert property (@(posedge clk_i) disable iff (rst_i)
                   ($past(state_r==IDLE && read_s))
                   |-> (state_r==ACK && ack_o==1'b1 &&
                        (dat_o == ($past(adr_i)==BASE_ADDR ? {16'h0, $past(sw_bi)} : 32'h0))));

  // No immediate ack during READ accept cycle (previous cycle)
  assert property (@(posedge clk_i) disable iff (rst_i)
                   ($past(state_r==IDLE && read_s)) |-> $past(ack_o)==1'b0);

  // Immediate ack during WRITE accept cycle (previous cycle)
  assert property (@(posedge clk_i) disable iff (rst_i)
                   ($past(state_r==IDLE && write_s)) |-> $past(ack_o)==1'b1);

  // In ACK last cycle -> ack asserted now and state returns to IDLE
  assert property (@(posedge clk_i) disable iff (rst_i)
                   ($past(state_r==ACK)) |-> (ack_o==1'b1 && state_r==IDLE));

  // Ack causality: any ack must be due to being in ACK last cycle
  assert property (@(posedge clk_i) disable iff (rst_i)
                   (ack_o) |-> ($past(state_r)==ACK));

  // GPIO can change only on WRITE to BASE_ADDR accepted in IDLE
  assert property (@(posedge clk_i) disable iff (rst_i)
                   $changed(gpio_bo) |-> $past(state_r==IDLE && write_s && adr_i==BASE_ADDR));

  // Read data value correctness when targeting BASE_ADDR (upper 16 must be zero)
  assert property (@(posedge clk_i) disable iff (rst_i)
                   ($past(state_r==IDLE && read_s && adr_i==BASE_ADDR))
                   |-> (dat_o[31:16]==16'h0 && dat_o[15:0]==$past(sw_bi)));

  // Protocol: requests during ACK are deferred (not accepted until return to IDLE)
  // If a request is present while we were in ACK, we must go IDLE now and to ACK next
  assert property (@(posedge clk_i) disable iff (rst_i)
                   ($past(state_r==ACK) && (read_s || write_s))
                   |-> (state_r==IDLE) |=> (state_r==ACK));

  // --------------------
  // Coverage
  // --------------------
  cover property (@(posedge clk_i) disable iff (rst_i)
                  (state_r==IDLE && read_s && adr_i==BASE_ADDR) ##1 (ack_o && state_r==ACK));

  cover property (@(posedge clk_i) disable iff (rst_i)
                  (state_r==IDLE && read_s && adr_i!=BASE_ADDR) ##1 (ack_o && state_r==ACK));

  cover property (@(posedge clk_i) disable iff (rst_i)
                  (state_r==IDLE && write_s && adr_i==BASE_ADDR) ##1 (ack_o && state_r==ACK) ##1 (ack_o && state_r==IDLE));

  cover property (@(posedge clk_i) disable iff (rst_i)
                  (state_r==IDLE && write_s && adr_i!=BASE_ADDR) ##1 (ack_o && state_r==ACK) ##1 (ack_o && state_r==IDLE));

  // Back-to-back transactions
  cover property (@(posedge clk_i) disable iff (rst_i)
                  (state_r==IDLE && write_s) ##2 (state_r==IDLE && write_s));

  cover property (@(posedge clk_i) disable iff (rst_i)
                  (state_r==IDLE && read_s) ##2 (state_r==IDLE && read_s));

  cover property (@(posedge clk_i) disable iff (rst_i)
                  (state_r==IDLE && read_s) ##2 (state_r==IDLE && write_s));

  cover property (@(posedge clk_i) disable iff (rst_i)
                  (state_r==IDLE && write_s) ##2 (state_r==IDLE && read_s));

  // Request held through ACK (stb/cyc kept asserted across the ack cycle)
  cover property (@(posedge clk_i) disable iff (rst_i)
                  (state_r==IDLE && (read_s||write_s)) ##1 (state_r==ACK && (cyc_i && stb_i)) ##1 (state_r==IDLE && (read_s||write_s)));

endmodule

// Bind into DUT
bind gpio_wb gpio_wb_sva #(.BASE_ADDR(BASE_ADDR)) u_gpio_wb_sva (
  .clk_i, .rst_i,
  .dat_i, .dat_o, .adr_i, .we_i, .sel_i, .cyc_i, .stb_i, .ack_o,
  .sw_bi, .gpio_bo,
  .state_r
);