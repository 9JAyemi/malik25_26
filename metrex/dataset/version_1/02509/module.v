module pulse_generator #(
  parameter WIDTH=8
) (
  input clock,
  input reset,
  input enable,
  input [WIDTH-1:0] rate,
  input strobe_fast,
  output reg strobe_slow
);

  reg [WIDTH-1:0] counter;
  wire now = (counter == 1);
  
  always @(posedge clock)
    if(reset)
      counter <= 0; 
    else if (~enable)
      counter <= rate;
    else if(strobe_fast)
    begin
      if(now)
        counter <= rate;
      else 
        counter <= counter - 1;
    end

  always @*
    strobe_slow = now && enable && strobe_fast;

endmodule