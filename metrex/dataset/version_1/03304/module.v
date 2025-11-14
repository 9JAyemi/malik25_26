
module axis_async_frame_fifo_64 (
  input input_clk,
  input input_rst,
  input [63:0] input_axis_tdata,
  input [7:0] input_axis_tkeep,
  input input_axis_tvalid,
  input input_axis_tlast,
  input input_axis_tuser,
  output reg input_axis_tready,
  input output_clk,
  input output_rst,
  output reg [63:0] output_axis_tdata,
  output reg [7:0] output_axis_tkeep,
  output reg output_axis_tvalid,
  output reg output_axis_tlast,
  output output_axis_tready
);

  localparam DEPTH = 64;
  localparam ADDR_WIDTH = 6;
  localparam DATA_WIDTH = 64;

  reg [DATA_WIDTH - 1:0] buffer [DEPTH - 1:0];
  reg [ADDR_WIDTH - 1:0] write_ptr = 0, read_ptr = 0;

  always @(posedge input_clk) begin
    if (input_rst) begin
      write_ptr <= 0;
      input_axis_tready <= 1'b1; // Ready to accept data after reset
    end else if (input_axis_tvalid && input_axis_tready) begin
      buffer[write_ptr] <= input_axis_tdata; // Write data to buffer
      write_ptr <= write_ptr + 1'b1; // Increment write pointer
    end
  end

  always @(posedge output_clk) begin
    if (output_rst) begin
      read_ptr <= 0;
      output_axis_tvalid <= 1'b0; // Output not valid after reset
    end else if (!output_axis_tvalid || (output_axis_tvalid && output_axis_tready)) begin
      output_axis_tdata <= buffer[read_ptr]; // Read data from buffer
      output_axis_tkeep <= input_axis_tkeep;
      output_axis_tlast <= input_axis_tlast;
      read_ptr <= read_ptr + 1'b1; // Increment read pointer
      output_axis_tvalid <= 1'b1; // Mark output as valid
    end
  end

  assign output_axis_tready = (read_ptr == write_ptr) ? 1'b0 : 1'b1; // Assert tready when FIFO is not full

endmodule