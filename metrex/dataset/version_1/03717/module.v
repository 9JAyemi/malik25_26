
module spi_shift (
  input clk, rst, go, pos_edge, neg_edge, rx_negedge, tx_negedge, lsb, s_clk,
  input [17:0] p_in,
  input [7:0] len,
  output reg tip, 
  output last, //reg last; cannot be driven by primitives or continuous assignment.
  output reg [17:0] p_out,
  output reg s_out
);

  parameter Tp = 1;
  parameter SPI_CHAR_LEN_BITS = 8;
  parameter SPI_MAX_CHAR = 18;

  reg [SPI_CHAR_LEN_BITS:0] cnt;
  reg [SPI_MAX_CHAR-1:0] data;
  wire [SPI_CHAR_LEN_BITS:0] tx_bit_pos;
  wire [SPI_CHAR_LEN_BITS:0] rx_bit_pos;
  wire rx_clk;
  wire tx_clk;

  assign tx_bit_pos = lsb ? {!(|len), len} - cnt : cnt - {{SPI_CHAR_LEN_BITS{1'b0}},1'b1};
  assign rx_bit_pos = lsb ? {!(|len), len} - (rx_negedge ? cnt + {{SPI_CHAR_LEN_BITS{1'b0}},1'b1} : cnt) :
                            (rx_negedge ? cnt : cnt - {{SPI_CHAR_LEN_BITS{1'b0}},1'b1});

  //assign last = !(|cnt);
  reg last_int;
  always @(posedge clk or posedge rst) begin
    if(rst) last_int <= #Tp 1'b0;
    else last_int <= #Tp !(|cnt);
  end
  assign last = last_int;

  assign rx_clk = (rx_negedge ? neg_edge : pos_edge) && (!last || s_clk);
  assign tx_clk = (tx_negedge ? neg_edge : pos_edge) && !last;

  always @(posedge clk or posedge rst) begin
    if(rst) cnt <= #Tp {SPI_CHAR_LEN_BITS+1{1'b0}};
    else begin
      if(tip) cnt <= #Tp pos_edge ? (cnt - {{SPI_CHAR_LEN_BITS{1'b0}}, 1'b1}) : cnt;
      else cnt <= #Tp !(|len) ? {1'b1, {SPI_CHAR_LEN_BITS{1'b0}}} : {1'b0, len};
    end
  end

  always @(posedge clk or posedge rst) begin
    if (rst) s_out <= #Tp 1'b0;
    else s_out <= #Tp (tx_clk || !tip) ? data[tx_bit_pos[SPI_CHAR_LEN_BITS-1:0]] : s_out;
  end

  always @(posedge s_clk or posedge rst) begin
    if (rst) data <= #Tp {SPI_MAX_CHAR{1'b0}};
    else data <= #Tp {data[SPI_MAX_CHAR-2:0], p_in};
  end

  always @(posedge s_clk or posedge rst) begin
    if (rst) p_out <= #Tp {18{1'b0}};
    else p_out <= #Tp {data[17:0], 1'b0};
  end

  always @(posedge clk or posedge rst) begin
    if (rst) tip <= #Tp 1'b0;
    else if (go && ~tip) tip <= #Tp 1'b1;
    else if (tip && last && pos_edge) tip <= #Tp 1'b0;
  end

endmodule