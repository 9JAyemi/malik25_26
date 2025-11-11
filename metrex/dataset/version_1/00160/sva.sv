// SVA checker for module memory
module memory_sva
  #(parameter MEM_SIZE = 4096,
    parameter ADDR_WIDTH = 12,
    parameter DATA_WIDTH = 12)
(
  input logic                    clk,
  input logic                    we,
  input logic [ADDR_WIDTH-1:0]   addr,
  input logic [DATA_WIDTH-1:0]   din,
  input logic [DATA_WIDTH-1:0]   dout
);

  // Static sanity
  initial assert (MEM_SIZE <= (1<<ADDR_WIDTH))
    else $error("ADDR_WIDTH too small for MEM_SIZE");

  default clocking cb @(posedge clk); endclocking

  // Reference model (scoreboard)
  logic [DATA_WIDTH-1:0] ref_mem [0:MEM_SIZE-1];
  always_ff @(posedge clk) if (we) ref_mem[addr] <= din;

  // First-cycle guard
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Basic input integrity
  a_no_x_we:        assert property (!$isunknown(we));
  a_no_x_on_write:  assert property (we  |-> !$isunknown({addr,din}));
  a_no_x_on_read:   assert property (!we |-> !$isunknown(addr));
  a_addr_in_range:  assert property (!$isunknown(addr) |-> addr < MEM_SIZE);

  // Functional correctness
  // Read returns stored data (same-cycle read path)
  a_read_data:      assert property (!we |-> (dout === ref_mem[addr]));
  // Write does not change dout (no read-during-write)
  a_dout_stable_wr: assert property (past_valid && we |-> $stable(dout));

  // Targeted scenario checks
  // Write then next-cycle read same address returns written data
  a_wr_rd_b2b: assert property (past_valid && we ##1 (!we && addr == $past(addr)) |-> (dout === $past(din)));
  // Two writes to same address; read returns last write
  a_two_wr_last_wins: assert property (
    past_valid &&
    we ##1 (we && addr == $past(addr)) ##1
    (!we && addr == $past(addr,1)) |-> (dout === $past(din))
  );

  // Coverage
  c_write:               cover property (we);
  c_read:                cover property (!we);
  c_wr_rd_b2b:           cover property (we ##1 (!we && addr == $past(addr)) && (dout === $past(din)));
  c_two_wr_last_wins:    cover property (we ##1 (we && addr == $past(addr)) ##1 (!we && addr == $past(addr,1)) && (dout === $past(din)));
  c_low_addr_path:       cover property (we && addr==0       ##1 !we && addr==0       && (dout === $past(din)));
  c_high_addr_path:      cover property (we && addr==MEM_SIZE-1 ##1 !we && addr==MEM_SIZE-1 && (dout === $past(din)));
  c_back_to_back_reads:  cover property (!we ##1 !we);
  c_back_to_back_writes: cover property (we  ##1 we);

endmodule

// Bind into DUT
bind memory memory_sva #(.MEM_SIZE(MEM_SIZE), .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH))
  memory_sva_i(.clk(clk), .we(we), .addr(addr), .din(din), .dout(dout));