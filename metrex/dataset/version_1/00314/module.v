module decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_blk_mem_gen_v8_3_4
  (dout,
   clk,
   tmp_ram_rd_en,
   E,
   out,
   \gc0.count_d1_reg[7] ,
   Q,
   din);
  output [63:0]dout;
  input clk;
  input tmp_ram_rd_en;
  input [0:0]E;
  input [0:0]out;
  input [7:0]\gc0.count_d1_reg[7] ;
  input [7:0]Q;
  input [63:0]din;

  wire [0:0]E;
  wire [7:0]Q;
  wire clk;
  wire [63:0]din;
  wire [63:0]dout;
  wire [7:0]\gc0.count_d1_reg[7] ;
  wire [0:0]out;
  wire tmp_ram_rd_en;

  // Create a tmp_ram block with a capacity of 256 bytes
  reg [63:0] tmp_ram [0:255];

  // Write data to tmp_ram block
  always @(posedge clk) begin
    if (tmp_ram_rd_en == 1'b0) begin
      tmp_ram[Q] <= din;
    end
  end

  // Read data from tmp_ram block
  assign dout = tmp_ram[out];

endmodule