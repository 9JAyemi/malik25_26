// SVA for serial_fifo_buffer
// Bind into the DUT to check core behavior and provide key coverage

module serial_fifo_buffer_sva (
  input  logic         s_axi_aclk,
  input  logic         s_axi_aresetn,

  // DUT I/Os and internals
  input  logic         fifo_wr,
  input  logic         fifo_Read,
  input  logic  [7:0]  s_axi_wdata,
  input  logic  [7:0]  Q,
  input  logic  [3:0]  write_ptr,
  input  logic  [3:0]  read_ptr,
  input  logic         tx_Buffer_Full,
  input  logic         tx_Buffer_Empty,

  input  logic         mux_sel_reg_0,
  input  logic  [7:0]  tx_DataBits,
  input  logic         p_4_in,
  input  logic         mux_Out,

  input  logic         tx_Start,
  input  logic         tx_Data_Enable_reg,
  input  logic         tx_Start0
);

  default clocking cb @(posedge s_axi_aclk); endclocking
  default disable iff (!s_axi_aresetn)

  function automatic logic [3:0] inc4(logic [3:0] x);
    return (x==4'd15) ? 4'd0 : (x + 4'd1);
  endfunction

  // Shadow memory to check read data (avoids peeking DUT fifo)
  logic [7:0] shadow [0:15];
  always_ff @(posedge s_axi_aclk) begin
    if (!s_axi_aresetn) begin
      for (int i=0;i<16;i++) shadow[i] <= '0;
    end else begin
      if (fifo_wr && !tx_Buffer_Full) shadow[write_ptr] <= s_axi_wdata;
    end
  end

  // Reset state
  assert property ( !s_axi_aresetn |-> (write_ptr==4'd0 && read_ptr==4'd0 && !tx_Buffer_Full) );

  // Pointer updates
  assert property ( (fifo_wr && !tx_Buffer_Full) |=> write_ptr == inc4($past(write_ptr)) );
  assert property ( !(fifo_wr && !tx_Buffer_Full) |=> write_ptr == $past(write_ptr) );
  assert property ( fifo_Read |=> read_ptr == inc4($past(read_ptr)) );
  assert property ( !fifo_Read |=> read_ptr == $past(read_ptr) );

  // Full flag behavior
  assert property ( fifo_Read |=> !tx_Buffer_Full );
  assert property ( (fifo_wr && !tx_Buffer_Full && !fifo_Read && (write_ptr==read_ptr)) |=> tx_Buffer_Full );
  assert property ( (tx_Buffer_Full && fifo_wr) |=> write_ptr == $past(write_ptr) ); // no write when full

  // Empty output definition
  assert property ( tx_Buffer_Empty == ~tx_Buffer_Full );

  // Data read-out correctness (excluding same-cycle RW to same entry)
  assert property (
    fifo_Read && !(fifo_wr && !tx_Buffer_Full && (write_ptr==read_ptr))
    |=> Q == shadow[$past(read_ptr)]
  );

  // Combinational outputs
  assert property ( mux_Out == (mux_sel_reg_0 ? tx_DataBits[0] : p_4_in) );
  assert property ( tx_Start0 == (tx_Start && tx_Data_Enable_reg) );

  // Coverage
  cover property ( !s_axi_aresetn ##1 s_axi_aresetn );
  cover property ( s_axi_aresetn && (fifo_wr && !tx_Buffer_Full) );
  cover property ( s_axi_aresetn && fifo_Read );
  cover property ( (write_ptr==4'd15) && (fifo_wr && !tx_Buffer_Full) ##1 (write_ptr==4'd0) );
  cover property ( (read_ptr==4'd15) && fifo_Read ##1 (read_ptr==4'd0) );
  cover property ( (fifo_wr && !tx_Buffer_Full && (write_ptr==read_ptr)) ##1 tx_Buffer_Full );
  cover property ( fifo_Read ##1 !tx_Buffer_Full );
  cover property ( mux_sel_reg_0==1'b0 ##1 mux_sel_reg_0==1'b1 );
  cover property ( tx_Start && tx_Data_Enable_reg && tx_Start0 );

endmodule

bind serial_fifo_buffer serial_fifo_buffer_sva u_sva(
  .s_axi_aclk(s_axi_aclk),
  .s_axi_aresetn(s_axi_aresetn),

  .fifo_wr(fifo_wr),
  .fifo_Read(fifo_Read),
  .s_axi_wdata(s_axi_wdata),
  .Q(Q),
  .write_ptr(write_ptr),
  .read_ptr(read_ptr),
  .tx_Buffer_Full(tx_Buffer_Full),
  .tx_Buffer_Empty(tx_Buffer_Empty),

  .mux_sel_reg_0(mux_sel_reg_0),
  .tx_DataBits(tx_DataBits),
  .p_4_in(p_4_in),
  .mux_Out(mux_Out),

  .tx_Start(tx_Start),
  .tx_Data_Enable_reg(tx_Data_Enable_reg),
  .tx_Start0(tx_Start0)
);