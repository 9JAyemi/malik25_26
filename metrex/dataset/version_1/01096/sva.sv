// Bindable SVA checker for memory_64bit_4bank
module memory_64bit_4bank_sva (
  input        clk,
  input [63:0] din,
  input        wr_en,
  input  [1:0] wr_addr,
  input        rd_en,
  input  [1:0] rd_addr,
  input [63:0] dout,
  input        full
);
  default clocking cb @(posedge clk); endclocking

  function automatic [63:0] swap16(input [63:0] x);
    swap16 = {x[15:0], x[31:16], x[47:32], x[63:48]};
  endfunction

  logic [63:0] scb [3:0];
  logic [3:0]  valid;

  initial valid = '0;

  // Simple golden model consistent with DUT's lane mapping and read-old collision semantics
  always_ff @(posedge clk) begin
    if (wr_en) begin
      scb[wr_addr]  <= swap16(din);
      valid[wr_addr] <= 1'b1;
    end
  end

  // A1: dout only changes when rd_en is asserted
  assert property (cb !rd_en |-> $stable(dout));

  // A2: full must be tied-low
  assert property (cb full == 1'b0);

  // A3: Read returns current bank contents (when initialized)
  assert property (cb (rd_en && valid[rd_addr]) |-> (dout == scb[rd_addr] && !$isunknown(dout)));

  // A4: Same-cycle write+read to same bank returns old data
  assert property (cb (rd_en && wr_en && (rd_addr==wr_addr) && valid[rd_addr]) |-> dout == $past(scb[rd_addr]));

  // A5: Same-cycle write to other bank does not affect read result
  assert property (cb (rd_en && wr_en && (rd_addr!=wr_addr) && valid[rd_addr]) |-> dout == scb[rd_addr]);

  // COV: address space and key scenarios
  cover property (cb wr_en && rd_en && (rd_addr==wr_addr));   // collision
  cover property (cb wr_en && rd_en && (rd_addr!=wr_addr));   // independent
  cover property (cb wr_en && wr_addr==2'd0);
  cover property (cb wr_en && wr_addr==2'd1);
  cover property (cb wr_en && wr_addr==2'd2);
  cover property (cb wr_en && wr_addr==2'd3);
  cover property (cb rd_en && rd_addr==2'd0);
  cover property (cb rd_en && rd_addr==2'd1);
  cover property (cb rd_en && rd_addr==2'd2);
  cover property (cb rd_en && rd_addr==2'd3);
endmodule

// Bind into the DUT
bind memory_64bit_4bank memory_64bit_4bank_sva sva_i(
  .clk(clk),
  .din(din),
  .wr_en(wr_en),
  .wr_addr(wr_addr),
  .rd_en(rd_en),
  .rd_addr(rd_addr),
  .dout(dout),
  .full(full)
);