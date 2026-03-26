module full_synchronizer #(
  parameter WIDTH = 1
)(
  input  wire             clk,
  input  wire             reset,
  input  wire [WIDTH-1:0] datain,
  output wire [WIDTH-1:0] dataout
);

  reg [1:0] metastable;
  always @(posedge clk) begin
    if (reset) begin
      metastable <= 2'b00;
    end else begin
      metastable <= {metastable[0], datain[0]};
    end
  end
  
  assign dataout = metastable[1:0];
endmodule

module pipeline_stall #(
  parameter WIDTH = 1,
  parameter DEPTH = 2
)(
  input  wire             clk,
  input  wire             reset,
  input  wire [WIDTH-1:0] datain,
  output wire [WIDTH-1:0] dataout
);

  reg [1:0] metastable;
  always @(posedge clk) begin
    if (reset) begin
      metastable <= 2'b00;
    end else begin
      metastable <= {metastable[0], datain[0]};
    end
  end
  
  assign dataout = metastable[1:0];
endmodule