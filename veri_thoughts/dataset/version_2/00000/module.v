module mux_4to1_case (
  input [3:0] in0,
  input [3:0] in1,
  input [3:0] in2,
  input [3:0] in3,
  input [1:0] sel,
  output [3:0] out
);
  
  reg [3:0] mux_out;
  
  always @(*) begin
    case(sel)
      2'b00: mux_out = in0;
      2'b01: mux_out = in1;
      2'b10: mux_out = in2;
      2'b11: mux_out = in3;
      default: mux_out = 4'b0;
    endcase
  end
  
  assign out = mux_out;
  
endmodule
module mux_4to1_if (
  input [3:0] in0,
  input [3:0] in1,
  input [3:0] in2,
  input [3:0] in3,
  input [1:0] sel,
  output [3:0] out
);
  
  reg [3:0] mux_out;
  
  always @(*) begin
    if(sel == 2'b00) begin
      mux_out = in0;
    end
    else if(sel == 2'b01) begin
      mux_out = in1;
    end
    else if(sel == 2'b10) begin
      mux_out = in2;
    end
    else if(sel == 2'b11) begin
      mux_out = in3;
    end
    else begin
      mux_out = 4'b0;
    end
  end
  
  assign out = mux_out;
  
endmodule
