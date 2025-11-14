// SVA for bw_r_idct_array
module bw_r_idct_array_sva #(parameter ADDR_W=7, DATA_W=33) (
  input clk,
  input we,
  input [DATA_W-1:0] wr_data,
  input [ADDR_W-1:0] addr,
  input [3:0] dec_wrway_y,
  input [1:0] way,
  input [DATA_W-1:0] rd_data
);

  default clocking cb @(negedge clk); endclocking

  // Sanity/known checks
  assert property ( !$isunknown(we) );
  assert property ( we  |-> !$isunknown({addr,wr_data}) );
  assert property ( !we |-> !$isunknown(addr) );
  assert property ( !$isunknown({dec_wrway_y,way}) );

  // rd_data is held on write cycles (no update when we==1)
  assert property ( we |-> rd_data == $past(rd_data) );

  // Simple reference model for functional checks
  logic [DATA_W-1:0] ref_mem [0:(1<<ADDR_W)-1];
  bit                ref_vld [0:(1<<ADDR_W)-1];
  logic [DATA_W-1:0] exp_rd;
  bit                exp_vld;

  always_ff @(negedge clk) begin
    if (we) begin
      ref_mem[addr] <= wr_data;
      ref_vld[addr] <= 1'b1;
    end else begin
      exp_rd  <= ref_mem[addr];
      exp_vld <= ref_vld[addr];
    end
  end

  // When prior cycle was a valid read, rd_data must equal expected value
  assert property ( $past(!we && exp_vld) |-> rd_data == $past(exp_rd) );

  // Read-after-write (next cycle, same address) returns the written data
  assert property ( we ##1 (!we && addr==$past(addr)) |-> rd_data==$past(wr_data) );

  // Two writes to same address: later read returns last data (last-wins)
  property two_writes_then_read_last_wins;
    logic [ADDR_W-1:0] a;
    logic [DATA_W-1:0] d2;
    (we, a=addr) ##1 (we && addr==a, d2=wr_data) ##[1:$] (!we && addr==a) |-> rd_data==d2;
  endproperty
  assert property (two_writes_then_read_last_wins);

  // Coverage
  cover property ( we );
  cover property ( !we );
  cover property ( we ##1 !we );                          // write then read
  cover property ( we && addr=={ADDR_W{1'b0}} );          // addr=0 write
  cover property ( we && addr=={ADDR_W{1'b1}} );          // addr=max write
  cover property ( $changed(dec_wrway_y) );
  cover property ( $changed(way) );

  // Write -> (1..N) -> Read same address observed
  property write_then_later_read_same_addr;
    logic [ADDR_W-1:0] a;
    (we, a=addr) ##[1:$] (!we && addr==a);
  endproperty
  cover property (write_then_later_read_same_addr);

endmodule

bind bw_r_idct_array bw_r_idct_array_sva #(.ADDR_W(7), .DATA_W(33))
  i_bw_r_idct_array_sva (.clk(clk), .we(we), .wr_data(wr_data), .addr(addr),
                         .dec_wrway_y(dec_wrway_y), .way(way), .rd_data(rd_data));