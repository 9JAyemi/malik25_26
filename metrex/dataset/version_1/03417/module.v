module axis_srl_fifo(
  input clk, rst,
  input [7:0] input_axis_tdata,
  input input_axis_tvalid, input_axis_tlast, input_axis_tuser,
  output reg input_axis_tready,
  output reg [7:0] output_axis_tdata,
  output reg output_axis_tvalid, output_axis_tlast, output_axis_tuser,
  input output_axis_tready,
  output reg [2:0] count
);

  parameter DEPTH = 4;
  parameter DATA_WIDTH = 8;

  reg [DATA_WIDTH-1:0] fifo [0:DEPTH-1];
  reg [2:0] head = 3'b0;
  reg [2:0] tail = 3'b0;
  reg [2:0] count_reg = 3'b0;

  always @(posedge clk) begin
    if (rst) begin
      head <= 3'b0;
      tail <= 3'b0;
      count_reg <= 3'b0;
    end else begin
      if (input_axis_tvalid && input_axis_tready) begin
        fifo[head] <= input_axis_tdata;
        head <= (head == 3'b111) ? 3'b0 : head + 1;
        count_reg <= (count_reg == 3'b100) ? 3'b100 : count_reg + 1;
      end
      if (output_axis_tready && count_reg > 3'b0) begin
        output_axis_tdata <= fifo[tail];
        output_axis_tvalid <= 1;
        output_axis_tlast <= (count_reg == 3'b1) && input_axis_tlast;
        output_axis_tuser <= input_axis_tuser;
        tail <= (tail == 3'b111) ? 3'b0 : tail + 1;
        count_reg <= count_reg - 1;
      end else begin
        output_axis_tvalid <= 0;
      end
    end
    input_axis_tready <= (count_reg < 3'b100) ? 1 : 0;
    count <= count_reg;
  end

endmodule