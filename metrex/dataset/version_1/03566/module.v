

module util_delay #(

  parameter DATA_WIDTH = 1,
  parameter DELAY_CYCLES = 1) (

  input                             clk,
  input                             reset,
  input                             din,
  output  [DATA_WIDTH-1:0]          dout);

  reg     [DATA_WIDTH-1:0]          dbuf[0:(DELAY_CYCLES-1)];

  always @(posedge clk) begin
    if (reset) begin
      dbuf[0] <= 0;
    end else begin
      dbuf[0] <= din;
    end
  end

  generate
  genvar i;
    for (i = 1; i < DELAY_CYCLES; i=i+1) begin:register_pipe
      always @(posedge clk) begin
        if (reset) begin
          dbuf[i] <= 0;
        end else begin
          dbuf[i] <= dbuf[i-1];
        end
      end
    end
  endgenerate

  assign dout = dbuf[(DELAY_CYCLES-1)];

endmodule
