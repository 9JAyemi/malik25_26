
module audio_codec (
  input [n-1:0] in,
  input clk, 
  input ctrl_in,
  output [m-1:0] out,
  output reg ctrl_out 
);

parameter n = 16; 
parameter m = 16; 
parameter fs = 44100; 
parameter bitrate = 128; 
parameter mode = "MP3"; 

reg [m-1:0] out_reg; 
assign out = out_reg; 

always @ (posedge clk) begin
  if (ctrl_in == 1'b0) begin
    ctrl_out <= 1'b0; 
    out_reg <= {16{1'b0}}; 
  end else begin
    ctrl_out <= 1'b1; 
    out_reg <= {16{1'b0}}; 
  end
end

endmodule