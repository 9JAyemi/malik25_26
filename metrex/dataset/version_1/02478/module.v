module one_hot_state_machine (
  input clk, // clock signal
  input rst, // reset signal
  input [n-1:0] in, // n-bit input signal
  output [n-1:0] out // n-bit output signal
);

parameter n = 4; // number of bits in the input and output signals

// define the states as unique one-hot binary codes
parameter STATE0 = 4'b0001;
parameter STATE1 = 4'b0010;
parameter STATE2 = 4'b0100;
parameter STATE3 = 4'b1000;

// define the state register
reg [n-1:0] state;

// define the next state logic
always @ (posedge clk, posedge rst)
begin
  if (rst) // reset the state to STATE0
    state <= STATE0;
  else // determine the next state based on the input signal and the current state
    case (state)
      STATE0: state <= (in == 0) ? STATE0 : STATE1;
      STATE1: state <= (in == 0) ? STATE2 : STATE3;
      STATE2: state <= (in == 0) ? STATE0 : STATE1;
      STATE3: state <= (in == 0) ? STATE2 : STATE3;
    endcase
end

// define the output logic
assign out = state;

endmodule