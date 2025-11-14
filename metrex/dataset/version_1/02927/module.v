


module digitalfilter(output out, input clk, input ce, input in);
  
  reg [5:0] taps = 6'b000000;
  reg result = 0;
  
  assign out = result;
  
 
  always @(posedge clk)
  begin
    if(ce)
      begin
        taps[5] <= taps[4];
        taps[4] <= taps[3];
    	taps[3] <= taps[2];
    	taps[2] <= taps[1];
    	taps[1] <= taps[0];
        taps[0] <= in;
      end
    if(taps[2] & taps[3] & taps[4] & taps[5])
      result <= 1;
    if(~taps[2] & ~taps[3] & ~taps[4] & ~taps[5])
      result <= 0;
  end

 
  
endmodule


module graycode2(
  output up,
  output down,
  input clk,
  input freeze,
  input [1:0] tach);
  
  reg [1:0] last = 0;
  reg u = 0;
  reg d = 0;
  
  
  wire [3:0] encodedstate; 
  
  
  assign encodedstate = {tach, last};
  assign up = u;
  assign down = d;
  
  always @(posedge clk) begin
    u <= 0;
    d <= 0;
    if(~freeze) begin
      case(encodedstate) 
        4'b0000, 4'b1111,
        4'b1010,
        4'b0101:
          begin
          end
        4'b0100, 4'b1101,
        4'b1011,
        4'b0010:
          begin
            last <= tach;
            u <= 1;
            d <= 0;  
          end
        4'b0001, 4'b0111,
        4'b1110,
        4'b1000:
          begin
            last <= tach;
          	u <= 0;
            d <= 1;
          end
        4'b0011, 4'b1100,
        4'b0110,
        4'b1001:
          begin
          end 
        
        default: begin
          	u <= 1'bx;
          	d <= 1'bx;
          end
      endcase    
    end  
  end
  
  
endmodule

module udcounter16(
  output [15:0] counter,
  input clk,
  input up,
  input down);
  
  reg [15:0] result = 16'h0000;
  
  
  assign counter = result;
  
  always@(posedge clk) begin
    if(up) begin
      result <= result + 1;
    end
    if(down) begin
        result <= result - 1;
    end
  end
endmodule
 
module qc16(
  output [7:0] counth, 
  output [7:0] countl, 
  input [1:0] tach, 
  input clk,
  input freeze,
  input invphase);
 
  wire [15:0] counter;
  wire up;
  wire down;
  reg [1:0] adjtach;
  
  always @(*) begin
    if(invphase) begin
      adjtach[0] = tach[1];
      adjtach[1] = tach[0];
    end
    else begin
      adjtach[0] = tach[0];
      adjtach[1] = tach[1];
    end
  end
  
  
  graycode2 gc2(
    .clk(clk), 
    .freeze(freeze),
    .up(up), 
    .down(down), 
    .tach(adjtach));
    
  udcounter16 udc16(
    .clk(clk),
    .up(up),
    .down(down),
    .counter(counter));
  
  assign counth = counter[15:8];
  assign countl = counter[7:0];
 
endmodule


module tachcounter(
    output [7:0] countl,
	output [7:0] counth,
    input clk,
    input filterce,
    input freeze,
    input invphase,
    input [1:0] tach);
  
  wire [1:0] filttach;
  
  qc16 q16(
    .clk(clk),
    .tach(filttach),
    .freeze(freeze),
    .invphase(invphase),
    .countl(countl),
    .counth(counth));
  
  digitalfilter filterph0(
    .clk(clk),
    .ce(filterce),
    .in(tach[0]),
    .out(filttach[0]));
  
  digitalfilter filterph1(
    .clk(clk),
    .ce(filterce),
    .in(tach[1]),
    .out(filttach[1]));
  
endmodule   

