
module DBLC_3_64 ( PIN, GIN, PHI, POUT, GOUT );
input  [0:62] PIN;
input  [0:64] GIN;
input  PHI;
output [0:60] POUT;
output [0:64] GOUT;

wire [62:0] PIN_temp;
wire [64:0] GIN_temp;
wire [60:0] POUT_temp;

assign PIN_temp = {1'b0, PIN};
assign GIN_temp = {1'b0, GIN};

assign GOUT = GIN_temp;
assign POUT_temp = PHI ? GIN_temp[62:2] : PIN_temp[62:2];
assign POUT = POUT_temp[60:0];

endmodule