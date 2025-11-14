module wasca_external_sdram_controller_input_efifo_module (
  // inputs:
  clk,
  rd,
  reset_n,
  wr,
  wr_data,

  // outputs:
  almost_empty,
  almost_full,
  empty,
  full,
  rd_data
);

  output almost_empty;
  output almost_full;
  output empty;
  output full;
  output [42:0] rd_data;
  input clk;
  input rd;
  input reset_n;
  input wr;
  input [42:0] wr_data;

  wire almost_empty;
  wire almost_full;
  wire empty;
  reg [1:0] entries;
  reg [42:0] entry_0;
  reg [42:0] entry_1;
  wire full;
  reg rd_address;
  reg [42:0] rd_data;
  wire [1:0] rdwr;
  reg wr_address;
  assign rdwr = {rd, wr};
  assign full = entries == 2;
  assign almost_full = entries >= 1;
  assign empty = entries == 0;
  assign almost_empty = entries <= 1;
  
  always @(entry_0 or entry_1 or rd_address) begin
    case (rd_address)
      1'd0: rd_data = entry_0;
      1'd1: rd_data = entry_1;
      default: rd_data = 0;
    endcase
  end

  always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      wr_address <= 0;
      rd_address <= 0;
      entries <= 0;
    end else begin
      case (rdwr)
        2'd1: begin
          // Write data
          if (!full) begin
            entries <= entries + 1;
            wr_address <= (wr_address == 1) ? 0 : (wr_address + 1);
          end
        end
        2'd2: begin
          // Read data
          if (!empty) begin
            entries <= entries - 1;
            rd_address <= (rd_address == 1) ? 0 : (rd_address + 1);
          end
        end
        2'd3: begin
          wr_address <= (wr_address == 1) ? 0 : (wr_address + 1);
          rd_address <= (rd_address == 1) ? 0 : (rd_address + 1);
        end
        default: begin
        end
      endcase
    end
  end

  always @(posedge clk) begin
    //Write data
    if (wr & !full) begin
      case (wr_address)
        1'd0: entry_0 <= wr_data;
        1'd1: entry_1 <= wr_data;
        default: begin
        end
      endcase
    end
  end

endmodule