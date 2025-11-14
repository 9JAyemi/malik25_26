
module fifo_buffer #(
  parameter DATA_WIDTH          = 32,
  parameter FIFO_WIDTH          = 8
)(
  input                             rst,
  input       [31:0]                test_id,

  //write side
  input                             WR_CLK,
  output                            WR_RDY,
  input                             WR_ACT,
  output      [23:0]                WR_SIZE,
  input                             WR_STB,
  input       [DATA_WIDTH - 1: 0]   WR_DATA,
  output                            WR_STARVED,

  //read side
  input                             RD_CLK,
  input                             RD_STB,
  output                            RD_RDY,
  input                             RD_ACT,
  output      [23:0]                RD_SIZE,
  output      [DATA_WIDTH - 1: 0]   RD_DATA,

  output                            RD_INACTIVE
);

//Local Parameters
localparam ADDR_WIDTH = FIFO_WIDTH;
localparam ADDR_MASK  = (1 << ADDR_WIDTH) - 1;

//Registers/Wires
reg       [ADDR_WIDTH-1:0] wr_ptr = 0;
reg       [ADDR_WIDTH-1:0] rd_ptr = 0;
reg       [ADDR_WIDTH-1:0] count = 0;
reg                      wr_starved = 0;
reg                      rd_inactive = 1;
reg                      r_rst;

//Submodules
block_mem #(
  .DATA_WIDTH      (DATA_WIDTH),
  .ADDRESS_WIDTH   (ADDR_WIDTH)
) mem (
  .clk             (WR_CLK),
  .we              (WR_STB & WR_ACT & WR_RDY),
  .addr            (wr_ptr),
  .data            (WR_DATA),
  .q               (),
  .oe              (RD_STB & RD_ACT & RD_RDY),
  .oe_addr         (rd_ptr),
  .oe_data         (RD_DATA)
);

//Asynchronous Logic
always @ (*) r_rst = rst;

//Synchronous Logic
always @(posedge WR_CLK) begin
  if (r_rst) begin
    wr_ptr <= 0;
    rd_ptr <= 0;
    count <= 0;
    wr_starved <= 0;
    rd_inactive <= 1;
  end else begin
    if (WR_STB & WR_ACT & WR_RDY) begin
      wr_ptr <= wr_ptr + 1;
      count <= count + 1;
      rd_inactive <= 0;
      if (count == ADDR_MASK + 1) begin
        wr_starved <= 1;
      end
    end

    if (RD_STB & RD_ACT & RD_RDY) begin
      rd_ptr <= rd_ptr + 1;
      count <= count - 1;
      wr_starved <= 0;
      if (count == 0) begin
        rd_inactive <= 1;
      end
    end
  end
end

//Output Mux
assign WR_RDY = ~wr_starved;
assign RD_RDY = ~rd_inactive;
assign RD_INACTIVE = rd_inactive;
assign WR_STARVED = wr_starved;
assign WR_SIZE = ADDR_MASK + 1;
assign RD_SIZE = ADDR_MASK + 1 - count;

endmodule
module block_mem #(
  parameter DATA_WIDTH      = 32,
  parameter ADDRESS_WIDTH   = 8
)(
  input                             clk,
  input                             we,
  input       [ADDRESS_WIDTH-1:0] addr,
  input       [DATA_WIDTH - 1: 0] data,
  output      [DATA_WIDTH - 1: 0] q,
  input                             oe,
  input       [ADDRESS_WIDTH-1:0] oe_addr,
  output      [DATA_WIDTH - 1: 0] oe_data
);

//Registers/Wires
reg       [DATA_WIDTH - 1: 0]   mem [0:(1 << ADDRESS_WIDTH) - 1];
reg       [DATA_WIDTH - 1: 0]   q_reg;
reg       [DATA_WIDTH - 1: 0]   oe_data_reg;

//Write Logic
always @(posedge clk) begin
  if (we) begin
    mem[addr] <= data;
  end
end

//Read Logic
always @(*) begin
  q_reg = mem[addr];
end

//Output Logic
assign q = q_reg;

//Output Enable Logic
always @(*) begin
  if (oe) begin
    oe_data_reg = mem[oe_addr];
  end else begin
    oe_data_reg = 0;
  end
end

assign oe_data = oe_data_reg;

endmodule