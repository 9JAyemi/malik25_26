// SVA checker for onchip_trace_mem
// Concise, high-quality checks + targeted coverage

module onchip_trace_mem_sva #(
  parameter int WIDTH       = 64,
  parameter int DEPTH       = 512,
  parameter int ADDR_WIDTH  = 9,
  parameter int BYTE_WIDTH  = 8,
  parameter int BE_INPUT_W  = 9,                // width of DUT's byteenable port
  parameter string INIT_FILE = ""
) (
  input  logic                   clk,
  input  logic                   reset,
  input  logic                   reset_req,
  input  logic                   clken,
  input  logic                   chipselect,
  input  logic                   write,
  input  logic [ADDR_WIDTH-1:0]  address,
  input  logic [WIDTH-1:0]       writedata,
  input  logic [WIDTH-1:0]       readdata,
  input  logic [BE_INPUT_W-1:0]  byteenable
);

  // Derived
  localparam int BE_WIDTH = WIDTH / BYTE_WIDTH;

  // Static/elaboration sanity checks
  initial begin
    assert (WIDTH % BYTE_WIDTH == 0) else $error("WIDTH must be a multiple of BYTE_WIDTH");
    assert ($bits(address) == ADDR_WIDTH) else $error("address width != ADDR_WIDTH");
    assert (DEPTH <= (1<<ADDR_WIDTH)) else $error("DEPTH exceeds ADDR_WIDTH addressable space");
    assert (BE_INPUT_W >= BE_WIDTH) else $error("byteenable port too narrow for WIDTH/BYTE_WIDTH");
  end

  // Sampling and disable
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Local write enable (from DUT intent)
  logic wren_sva;
  assign wren_sva = chipselect & write;

  // Simple reference model for functional equivalence (read-before-write semantics)
  logic [WIDTH-1:0] mem_m [0:DEPTH-1];
  logic [WIDTH-1:0] rdata_exp;
  bit   [DEPTH-1:0] seen;
  bit               seen_r;
  bit               init_all;

  initial init_all = (INIT_FILE != "");

  always_ff @(posedge clk) begin
    // model uses same NBA semantics as DUT: read old mem, then perform write
    rdata_exp <= mem_m[address];
    seen_r    <= seen[address];
    if (wren_sva) begin
      mem_m[address] <= writedata;
      seen[address]  <= 1'b1;
    end
  end

  // Address range (covers both read and write use)
  ap_addr_in_range: assert property (address < DEPTH);

  // Byteenable policy: only full-line writes are supported by the RTL (partial ignored) -> flag them
  ap_be_full_on_write: assert property (wren_sva |-> (byteenable[BE_WIDTH-1:0] == {BE_WIDTH{1'b1}}));
  ap_be_upper_zero:    assert property (wren_sva |-> (BE_INPUT_W == BE_WIDTH) or (byteenable[BE_INPUT_W-1:BE_WIDTH] == '0));

  // No X/Z on critical inputs when writing
  ap_no_x_on_write_inputs: assert property (wren_sva |-> !$isunknown({address, writedata, byteenable[BE_WIDTH-1:0]}));

  // Functional equivalence: output matches golden model (read-before-write, 1R/1W port)
  ap_rdata_matches_model: assert property (readdata === rdata_exp);

  // No X on read for initialized locations (INIT_FILE present or location written before)
  ap_no_x_on_read_when_init: assert property ((init_all || seen_r) |-> !$isunknown(readdata));

  // Optional stability: if address stable and no write to that address in prior cycle, data is stable
  ap_stable_when_no_write_to_addr: assert property (
    $stable(address) && !($past(wren_sva) && ($past(address) == address)) |-> (readdata === $past(readdata))
  );

  // Coverage: basic ops, hazards, boundaries
  cv_any_write:                 cover property (wren_sva);
  cv_wr_lo_addr:               cover property (wren_sva && (address == '0));
  cv_wr_hi_addr:               cover property (wren_sva && (address == DEPTH-1));
  // Same-cycle write/read to same address returns old data (read-before-write)
  cv_same_cycle_wr_rd_old:     cover property (wren_sva && (readdata !== writedata));
  // Next-cycle read of written address returns new data
  cv_wr_then_rd_next_newdata:  cover property (wren_sva ##1 (address == $past(address)) && (readdata === $past(writedata)));

endmodule

// Bind into the DUT
bind onchip_trace_mem onchip_trace_mem_sva #(
  .WIDTH(WIDTH),
  .DEPTH(DEPTH),
  .ADDR_WIDTH(ADDR_WIDTH),
  .BYTE_WIDTH(BYTE_WIDTH),
  .BE_INPUT_W($bits(byteenable)),
  .INIT_FILE(INIT_FILE)
) u_onchip_trace_mem_sva (
  .clk(clk),
  .reset(reset),
  .reset_req(reset_req),
  .clken(clken),
  .chipselect(chipselect),
  .write(write),
  .address(address),
  .writedata(writedata),
  .readdata(readdata),
  .byteenable(byteenable)
);