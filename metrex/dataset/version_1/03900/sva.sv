// SVA for rw_manager_ram_csr
// Bindable assertions focusing on functional correctness, conciseness, and coverage.

module rw_manager_ram_csr_sva #(
  parameter int DATA_WIDTH = 32,
  parameter int ADDR_WIDTH = 2,
  parameter int NUM_WORDS  = 4
)(
  // DUT ports
  input  logic                   csr_clk,
  input  logic                   csr_ena,
  input  logic                   csr_din,
  input  logic                   ram_clk,
  input  logic                   wren,
  input  logic [DATA_WIDTH-1:0]  data,
  input  logic [ADDR_WIDTH-1:0]  wraddress,
  input  logic [ADDR_WIDTH-1:0]  rdaddress,
  input  logic [DATA_WIDTH-1:0]  q,
  input  logic                   csr_dout,
  // DUT internals we bind to
  input  logic                   int_clk,
  input  logic [DATA_WIDTH*NUM_WORDS-1:0] all_data
);

  localparam int DATA_COUNT = DATA_WIDTH*NUM_WORDS;

  // Helper: extract a word slice j from a flat vector
  function automatic logic [DATA_WIDTH-1:0] slice(input logic [DATA_COUNT-1:0] v, input int j);
    slice = v[(DATA_WIDTH*(j+1)-1) -: DATA_WIDTH];
  endfunction

  // Past-valid for int_clk domain
  bit intclk_seen;
  initial intclk_seen = 1'b0;
  always @(posedge int_clk) intclk_seen <= 1'b1;

  // int_clk must come from the selected clock
  assert property (@(posedge int_clk) (csr_ena ? $rose(ram_clk) : $rose(csr_clk)))
    else $error("int_clk edge does not coincide with selected clock edge");

  // CSR shift mode: shift left and insert csr_din at bit 0
  assert property (@(posedge int_clk) disable iff (!intclk_seen)
                   (!csr_ena) |-> (all_data[DATA_COUNT-1:1] == $past(all_data[DATA_COUNT-2:0]) &&
                                   all_data[0]               == $past(csr_din)))
    else $error("CSR shift operation incorrect");

  // RAM mode, no write: hold all_data
  assert property (@(posedge int_clk) disable iff (!intclk_seen)
                   (csr_ena && !wren) |-> all_data == $past(all_data))
    else $error("all_data changed without write in RAM mode");

  // RAM mode, write semantics per-row
  genvar j;
  generate
    for (j = 0; j < NUM_WORDS; j++) begin : gen_ram_checks
      // Selected row gets 'data'
      assert property (@(posedge int_clk) disable iff (!intclk_seen)
                       (csr_ena && wren && (wraddress == j)) |-> slice(all_data, j) == $past(data))
        else $error("Write data mismatch at row %0d", j);
      // Non-selected rows hold
      assert property (@(posedge int_clk) disable iff (!intclk_seen)
                       (csr_ena && wren && (wraddress != j)) |-> slice(all_data, j) ==
                         $past(all_data[(DATA_WIDTH*(j+1)-1) -: DATA_WIDTH]))
        else $error("Non-selected row changed at row %0d", j);
    end
  endgenerate

  // Out-of-range write address (if it can occur): no change
  assert property (@(posedge int_clk) disable iff (!intclk_seen)
                   (csr_ena && wren && (wraddress >= NUM_WORDS)) |-> all_data == $past(all_data))
    else $error("all_data changed on out-of-range wraddress");

  // q update: captures previous cycle's addressed row (1-cycle lag due to <= ordering)
  assert property (@(posedge int_clk) disable iff (!intclk_seen)
                   $past(rdaddress) < NUM_WORDS |-> q ==
                     $past(all_data[(DATA_WIDTH*($past(rdaddress)+1)-1) -: DATA_WIDTH]))
    else $error("q does not match expected previous row_data");

  // rdaddress must be in-range when sampling q
  assert property (@(posedge int_clk) rdaddress < NUM_WORDS)
    else $error("rdaddress out of range");

  // csr_dout samples MSB of all_data on csr_clk negedge
  assert property (@(negedge csr_clk) csr_dout === all_data[DATA_COUNT-1])
    else $error("csr_dout does not match MSB of all_data at csr_clk negedge");

  // Coverage
  // 1) Exercise CSR shift for several cycles
  cover property (@(posedge int_clk) !csr_ena ##1 !csr_ena ##1 !csr_ena);

  // 2) RAM write followed by readback through q (1-cycle later)
  cover property (@(posedge int_clk)
                  (csr_ena && wren) ##1 (rdaddress == $past(wraddress)) ##1 (q == $past(data)));

  // 3) Toggle csr_ena
  cover property (@(posedge csr_clk) $rose(csr_ena));
  cover property (@(posedge ram_clk) $fell(csr_ena));

endmodule

// Bind to the DUT. This bind assumes the assertion module is compiled with visibility
// to the DUT internals 'int_clk' and 'all_data'.
bind rw_manager_ram_csr
  rw_manager_ram_csr_sva #(
    .DATA_WIDTH(DATA_WIDTH),
    .ADDR_WIDTH(ADDR_WIDTH),
    .NUM_WORDS (NUM_WORDS)
  ) u_rw_manager_ram_csr_sva (
    .csr_clk   (csr_clk),
    .csr_ena   (csr_ena),
    .csr_din   (csr_din),
    .ram_clk   (ram_clk),
    .wren      (wren),
    .data      (data),
    .wraddress (wraddress),
    .rdaddress (rdaddress),
    .q         (q),
    .csr_dout  (csr_dout),
    .int_clk   (int_clk),
    .all_data  (all_data)
  );