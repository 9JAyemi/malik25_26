module jserialaddlab (
  input wire clk, 
  input wire reset, 
  input wire a, 
  input wire b, 
  output reg sum, 
  output reg carry, 
  output reg cout, 
  output reg [3:0] so, 
  output reg [2:0] count
);

  reg cut;
  reg cin;

  always @*
  begin
    sum = a ^ b ^ cin;
    cut = (a & b) | (a & cin) | (b & cin);
    carry = (count == 4'b100) ? 1'b0 : cut;
  end

  always @(posedge clk)
  begin
    if(reset)
      cin <= 1'b0;
    else
      cin <= carry;
  end

  always @(posedge clk)
  begin
    if(reset)
      cout <= 1'b0;
    else
      cout <= (count == 4'b100) ? (a & 4'b1000) : 1'b0;
  end

  always @(posedge clk)
  begin
    if(reset)
      so <= 4'b0;
    else
      so <= {sum, so[3:1]};
  end

  always @(posedge clk)
  begin
    if(reset)
      count <= 3'b0;
    else
      count <= (cut) ? count + 1 : 3'b0;
  end

endmodule