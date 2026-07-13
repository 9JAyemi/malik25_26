module data_comp_decomp #(
  parameter n = 8, // number of input bits
  parameter m = 4 // number of output bits
)(
  input [7:0] data_in, 
  output reg [3:0] data_out, 
  output reg valid
);

always @(*) begin
  valid = 1'b1; 
  
  case(data_in)
    8'b0000_0001: data_out = 4'b0001; // Symbol 1
    8'b0000_0010: data_out = 4'b0010; // Symbol 2
    8'b0000_0100: data_out = 4'b0011; // Symbol 3
    8'b0000_1000: data_out = 4'b0100; // Symbol 4
    default: begin
      data_out = 4'b0000; 
      valid = 1'b0;       
    end
  endcase
end

endmodule
