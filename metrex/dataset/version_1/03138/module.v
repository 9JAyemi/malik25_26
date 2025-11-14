module fifo_buffer #(
  parameter DATA_WIDTH = 8,
  parameter ADDRESS_WIDTH = 8,
  parameter FIFO_DEPTH = (1 << ADDRESS_WIDTH)
)
(
  // Reading port
  output reg [DATA_WIDTH-1:0] Data_out, 
  output reg Empty_out,
  input wire ReadEn_in,
  input wire RClk,        
  // Writing port	 
  input wire [DATA_WIDTH-1:0] Data_in,  
  output reg Full_out,
  input wire WriteEn_in,
  input wire WClk,
  input wire Clear_in
);

  // Internal connections & variables
  reg [DATA_WIDTH-1:0] Mem [0:FIFO_DEPTH-1]; 
  reg [ADDRESS_WIDTH-1:0] pNextWordToWrite, pNextWordToRead;
  wire EqualAddresses, NextWriteAddressEn, NextReadAddressEn;
  wire Set_Status, Rst_Status;
  reg Status;
  wire PresetFull, PresetEmpty;

  // Data ports logic
  always @ (posedge RClk) begin
    if (ReadEn_in && !Empty_out) begin
      Data_out <= Mem[pNextWordToRead];
    end
  end
  
  always @ (posedge WClk) begin
    if (WriteEn_in && !Full_out) begin
      Mem[pNextWordToWrite] <= Data_in;
    end
  end

  // FIFO addresses support logic
  assign NextWriteAddressEn = WriteEn_in && ~Full_out;
  assign NextReadAddressEn = ReadEn_in && ~Empty_out;

  // Addresses (Gray counters) logic
  always @ (posedge WClk) begin
    if (NextWriteAddressEn) begin
      pNextWordToWrite <= pNextWordToWrite + 1;
    end
  end

  always @ (posedge RClk) begin
    if (NextReadAddressEn) begin
      pNextWordToRead <= pNextWordToRead + 1;
    end
  end

  // 'EqualAddresses' logic
  assign EqualAddresses = (pNextWordToWrite == pNextWordToRead);

  // 'Quadrant selectors' logic
  assign Set_Status = (pNextWordToWrite[ADDRESS_WIDTH-2] ^ pNextWordToRead[ADDRESS_WIDTH-1]) &&
                      (pNextWordToWrite[ADDRESS_WIDTH-1] ^ pNextWordToRead[ADDRESS_WIDTH-2]);
  assign Rst_Status = (pNextWordToWrite[ADDRESS_WIDTH-2] ^ pNextWordToRead[ADDRESS_WIDTH-1]) &&
                      (pNextWordToWrite[ADDRESS_WIDTH-1] ^ pNextWordToRead[ADDRESS_WIDTH-2]);

  // 'Status' latch logic
  always @ (Set_Status, Rst_Status, Clear_in) begin
    if (Rst_Status || Clear_in) begin
      Status <= 0;
    end else if (Set_Status) begin
      Status <= 1;
    end
  end

  // 'Full_out' logic for the writing port
  assign PresetFull = Status && EqualAddresses;

  always @ (posedge WClk) begin
    if (PresetFull) begin
      Full_out <= 1;
    end else begin
      Full_out <= 0;
    end
  end
  
  // 'Empty_out' logic for the reading port
  assign PresetEmpty = ~Status && EqualAddresses;

  always @ (posedge RClk) begin
    if (PresetEmpty) begin
      Empty_out <= 1;
    end else begin
      Empty_out <= 0;
    end
  end

endmodule

module GrayCounter #(parameter WIDTH = 8) (
  output reg [WIDTH-1:0] GrayCount_out,
  input wire Enable_in,
  input wire Clear_in,
  input wire Clk
);

  always @ (posedge Clk) begin
    if (Clear_in) begin
      GrayCount_out <= 0;
    end else if (Enable_in) begin
      GrayCount_out <= GrayCount_out + 1;
    end
  end

endmodule