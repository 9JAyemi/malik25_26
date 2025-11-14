// SVA for Gpio
// Bindable checker that verifies address range, read/write effects,
// gpio function, reset behavior, and stability guarantees.

module Gpio_sva #(parameter int COUNT = 32, parameter int SIZE = 4)
(
  input  logic                   clk,
  input  logic                   reset,
  input  logic                   strobe,
  input  logic                   rw,          // bus direction: 1=write, 0=read
  input  logic [31:0]            addr,
  input  logic [31:0]            data_i,
  input  logic [31:0]            data_o,
  input  logic [COUNT-1:0]       gpio,
  input  logic [COUNT-1:0]       state [0:SIZE-1]   // DUT internal
);

  localparam int EN = 0, RW_IDX = 1, RS = 2, WS = 3;
  localparam int ADDR_W = (SIZE <= 1) ? 1 : $clog2(SIZE);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Address must be in range on any access
  assert property (strobe |-> (addr < SIZE));

  // Combinational gpio function (vector AND of enables)
  assert property (gpio == (state[EN] & state[RW_IDX] & state[WS]));

  // Read: next data_o is zero-extended state[addr] sampled at read cycle
  assert property (strobe && !rw && (addr < SIZE)
                   |=> (data_o[COUNT-1:0] == $past(state[$past(addr[ADDR_W-1:0])]))
                     && (data_o[31:COUNT] == '0));

  // Write: next state[addr] equals truncated data_i
  assert property (strobe && rw && (addr < SIZE)
                   |=> state[$past(addr[ADDR_W-1:0])] == $past(data_i[COUNT-1:0]));

  // On write, data_o must not change
  assert property (strobe && rw |=> data_o == $past(data_o));

  // Reset clears all state entries next cycle
  assert property (reset |=> (foreach (state[i]) (state[i] == '0)));

  // RS behavior: if not overwritten this cycle, RS becomes all 0 next cycle
  assert property (!(strobe && rw && (addr[ADDR_W-1:0] == RS)) |=> state[RS] == '0);

  // Idle: when no strobe, all state except RS holds value
  genvar i;
  generate
    for (i = 0; i < SIZE; i++) begin : g_idle_hold
      if (i != RS) begin
        assert property (!strobe |=> state[i] == $past(state[i]));
      end
    end
  endgenerate

  // Read: no state change except RS update
  generate
    for (i = 0; i < SIZE; i++) begin : g_read_hold
      if (i != RS) begin
        assert property (strobe && !rw |=> state[i] == $past(state[i]));
      end
    end
  endgenerate

  // Write: only targeted entry may change (plus RS via its implicit update)
  genvar k, j;
  generate
    for (k = 0; k < SIZE; k++) begin : g_write_target
      assert property (strobe && rw && (addr[ADDR_W-1:0] == k) |=> state[k] == $past(data_i[COUNT-1:0]));
      for (j = 0; j < SIZE; j++) begin : g_write_non_target
        if (j != k && j != RS) begin
          assert property (strobe && rw && (addr[ADDR_W-1:0] == k) |=> state[j] == $past(state[j]));
        end
      end
    end
  endgenerate

  // Coverage

  // Cover: write then read each address
  generate
    for (i = 0; i < SIZE; i++) begin : g_cov_wr_rd
      cover property (strobe && rw  && (addr[ADDR_W-1:0] == i)
                      ##1 strobe && !rw && (addr[ADDR_W-1:0] == i));
    end
  endgenerate

  // Cover: gpio toggles (some bit goes high then low)
  cover property ((gpio == '0) ##1 (gpio != '0) ##1 (gpio == '0));

  // Cover: RS written non-zero then auto-cleared
  cover property (strobe && rw && (addr[ADDR_W-1:0] == RS) && (data_i[COUNT-1:0] != '0)
                  ##1 (state[RS] != '0)
                  ##1 (state[RS] == '0));

endmodule

// Bind into DUT (tools must allow binding to internal 'state')
bind Gpio Gpio_sva #(.COUNT(COUNT), .SIZE(SIZE))
  gpio_sva_bind (.*,.state(state));