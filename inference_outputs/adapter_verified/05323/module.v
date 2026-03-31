module Counter (
    input Clock, Reset, Set, Load, Enable,
    input [Width-1:0] In,
    output reg [Width-1:0] Count
);

parameter Width = 32;
parameter Limited = 0;
parameter Down = 0;
parameter Initial = {Width{1'bx}};
parameter AsyncReset = 0;
parameter AsyncSet = 0;

wire NoLimit;

wire RegEnable;
wire [Width-1:0] RegIn;

assign NoLimit = !Limited;

assign RegEnable = Load | (Enable & (NoLimit | (Down ? Count : ~&Count)));
assign RegIn = Load ? In : (Down ? (Count - 1) : (Count + 1));

always @ (posedge Clock or posedge Reset)
    if (Reset)
        Count <= Initial;
    else if (RegEnable)
        Count <= RegIn;

endmodule

module Register (
    input Clock, Reset, Set, Enable,
    input [Width-1:0] In,
    output reg [Width-1:0] Out
);

parameter Width = 32;
parameter Initial = {Width{1'bx}};
parameter AsyncReset = 0;
parameter AsyncSet = 0;

always @ (posedge Clock or posedge Reset)
    if (Reset)
        Out <= Initial;
    else if (Enable)
        Out <= In;

endmodule