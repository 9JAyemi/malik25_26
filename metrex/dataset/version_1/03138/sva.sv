// SVA bind file for fifo_buffer and GrayCounter
// Focused, high-quality checks and concise functional coverage.

module fifo_buffer_sva #(
  parameter DATA_WIDTH = 8,
  parameter ADDRESS_WIDTH = 8,
  parameter FIFO_DEPTH = (1 << ADDRESS_WIDTH)
)(
  // DUT I/O
  input  wire                   RClk,
  input  wire                   WClk,
  input  wire                   Clear_in,
  input  wire                   ReadEn_in,
  input  wire                   WriteEn_in,
  input  wire [DATA_WIDTH-1:0]  Data_in,
  input  wire [DATA_WIDTH-1:0]  Data_out,
  input  wire                   Empty_out,
  input  wire                   Full_out,
  // DUT internals
  input  wire [ADDRESS_WIDTH-1:0] pNextWordToWrite,
  input  wire [ADDRESS_WIDTH-1:0] pNextWordToRead,
  input  wire                      EqualAddresses,
  input  wire                      NextWriteAddressEn,
  input  wire                      NextReadAddressEn,
  input  wire                      Status,
  input  wire                      PresetFull,
  input  wire                      PresetEmpty,
  input  wire                      Set_Status,
  input  wire                      Rst_Status
);

  // Clock init guards for $past/$changed
  bit w_init, r_init;
  initial begin w_init = 0; r_init = 0; end
  always @(posedge WClk) w_init <= 1;
  always @(posedge RClk) r_init <= 1;

  // Handshake enables must match their definitions
  assert property (@(posedge WClk) NextWriteAddressEn == (WriteEn_in && !Full_out));
  assert property (@(posedge RClk) NextReadAddressEn  == (ReadEn_in  && !Empty_out));

  // Pointer update behavior (increment on enable, hold otherwise)
  assert property (@(posedge WClk) w_init &&  NextWriteAddressEn |-> pNextWordToWrite == $past(pNextWordToWrite)+1);
  assert property (@(posedge WClk) w_init && !NextWriteAddressEn |-> pNextWordToWrite == $past(pNextWordToWrite));
  assert property (@(posedge RClk) r_init &&  NextReadAddressEn  |-> pNextWordToRead  == $past(pNextWordToRead)+1);
  assert property (@(posedge RClk) r_init && !NextReadAddressEn  |-> pNextWordToRead  == $past(pNextWordToRead));

  // EqualAddresses correctness in both domains
  assert property (@(posedge WClk) EqualAddresses == (pNextWordToWrite == pNextWordToRead));
  assert property (@(posedge RClk) EqualAddresses == (pNextWordToWrite == pNextWordToRead));

  // Flags must match their combinational presets
  assert property (@(posedge WClk) Full_out  == PresetFull);
  assert property (@(posedge RClk) Empty_out == PresetEmpty);

  // Flags should never be simultaneously asserted
  assert property (@(posedge WClk) !(Full_out && Empty_out));
  assert property (@(posedge RClk) !(Full_out && Empty_out));

  // No pointer advance on blocked operations
  assert property (@(posedge WClk) w_init && WriteEn_in && Full_out  |-> $stable(pNextWordToWrite));
  assert property (@(posedge RClk) r_init && ReadEn_in  && Empty_out |-> $stable(pNextWordToRead));

  // Data_out only updates on a valid read
  assert property (@(posedge RClk) r_init && $changed(Data_out) |-> (ReadEn_in && !Empty_out));

  // Status latch intended priority behavior
  assert property (@(posedge WClk) (Rst_Status || Clear_in) |-> Status == 1'b0);
  assert property (@(posedge RClk) (Rst_Status || Clear_in) |-> Status == 1'b0);
  assert property (@(posedge WClk) !Rst_Status && !Clear_in && Set_Status |-> Status == 1'b1);
  assert property (@(posedge RClk) !Rst_Status && !Clear_in && Set_Status |-> Status == 1'b1);

  // Critical: Set and Reset must not be asserted together (design bug catcher)
  assert property (@(posedge WClk) !(Set_Status && Rst_Status));
  assert property (@(posedge RClk) !(Set_Status && Rst_Status));

  // Lightweight data integrity scoreboard
  logic [DATA_WIDTH-1:0] shadow_mem [0:FIFO_DEPTH-1];
  bit                    shadow_vld [0:FIFO_DEPTH-1];

  integer i;
  initial for (i=0;i<FIFO_DEPTH;i++) begin shadow_mem[i] = '0; shadow_vld[i]=0; end

  always @(posedge WClk) if (NextWriteAddressEn) begin
    shadow_mem[pNextWordToWrite] <= Data_in;
    shadow_vld[pNextWordToWrite] <= 1'b1;
  end

  // When reading valid data, output must match shadow
  assert property (@(posedge RClk)
                    NextReadAddressEn && shadow_vld[pNextWordToRead]
                    |-> Data_out == shadow_mem[pNextWordToRead]);

  // Concise functional coverage
  cover property (@(posedge WClk) NextWriteAddressEn);
  cover property (@(posedge RClk) NextReadAddressEn);
  cover property (@(posedge WClk) $rose(Full_out));
  cover property (@(posedge RClk) $rose(Empty_out));
  cover property (@(posedge WClk) w_init && (&$past(pNextWordToWrite)) && NextWriteAddressEn
                  |-> pNextWordToWrite == '0); // wrap on write pointer
  cover property (@(posedge RClk) r_init && (&$past(pNextWordToRead)) && NextReadAddressEn
                  |-> pNextWordToRead == '0); // wrap on read pointer
  cover property (@(posedge WClk) EqualAddresses);
  cover property (@(posedge RClk) EqualAddresses);

endmodule

bind fifo_buffer fifo_buffer_sva #(
  .DATA_WIDTH(DATA_WIDTH),
  .ADDRESS_WIDTH(ADDRESS_WIDTH),
  .FIFO_DEPTH(FIFO_DEPTH)
) fifo_buffer_sva_i (
  // DUT I/O
  .RClk(RClk), .WClk(WClk), .Clear_in(Clear_in),
  .ReadEn_in(ReadEn_in), .WriteEn_in(WriteEn_in),
  .Data_in(Data_in), .Data_out(Data_out),
  .Empty_out(Empty_out), .Full_out(Full_out),
  // Internals
  .pNextWordToWrite(pNextWordToWrite),
  .pNextWordToRead(pNextWordToRead),
  .EqualAddresses(EqualAddresses),
  .NextWriteAddressEn(NextWriteAddressEn),
  .NextReadAddressEn(NextReadAddressEn),
  .Status(Status),
  .PresetFull(PresetFull),
  .PresetEmpty(PresetEmpty),
  .Set_Status(Set_Status),
  .Rst_Status(Rst_Status)
);

// SVA for GrayCounter (functional, not Gray-code-specific)
module GrayCounter_sva #(parameter WIDTH=8) (
  input wire                 Clk,
  input wire                 Enable_in,
  input wire                 Clear_in,
  input wire [WIDTH-1:0]     GrayCount_out
);
  bit init; initial init=0; always @(posedge Clk) init<=1;

  assert property (@(posedge Clk) Clear_in |-> GrayCount_out == '0);
  assert property (@(posedge Clk) init && !Clear_in &&  Enable_in |-> GrayCount_out == $past(GrayCount_out)+1);
  assert property (@(posedge Clk) init && !Clear_in && !Enable_in |-> GrayCount_out == $past(GrayCount_out));

  cover property (@(posedge Clk) Clear_in);
  cover property (@(posedge Clk) Enable_in);
  cover property (@(posedge Clk) !$isunknown(GrayCount_out) && (&$past(GrayCount_out)) && Enable_in && !Clear_in
                  |-> GrayCount_out == '0); // wrap
endmodule

bind GrayCounter GrayCounter_sva #(.WIDTH(WIDTH)) GrayCounter_sva_i (
  .Clk(Clk),
  .Enable_in(Enable_in),
  .Clear_in(Clear_in),
  .GrayCount_out(GrayCount_out)
);