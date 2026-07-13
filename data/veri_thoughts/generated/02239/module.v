
module Incrementer (inValue, outValue);
input [7:0] inValue;
output reg [7:0] outValue; // Change 'wire' to 'reg' to allow assignment

// add 1 to inValue using an adder
always @ (inValue)
begin
    if (inValue == 8'hFF) // if inValue is at maximum value
        outValue = 8'h00; // wrap around to 0
    else
        outValue = inValue + 1; // increment by 1
end

endmodule
