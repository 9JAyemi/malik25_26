`define size ((DATA_SIZE/4) * (2 ** (type - 1)))

module bit_reversal
#(
	parameter DATA_SIZE = 32
)
(
	output [DATA_SIZE - 1 : 0] data_out,
	input  [DATA_SIZE - 1 : 0] data_in,
	input  [1 : 0] rev_type
);


localparam NO_REVERSE = 2'b00; 
localparam BYTE       = 2'b01;
localparam HALF_WORD  = 2'b10;
localparam WORD       = 2'b11;

localparam TYPES = 4;

wire [DATA_SIZE - 1 : 0] data_reversed[0 : 3];


assign data_reversed[NO_REVERSE] = data_in; generate
	genvar i, type;
	for(type = 1 ; type < TYPES; type = type + 1)
		for(i = 0; i < DATA_SIZE; i = i + 1)
			begin
				if(i < `size)
					assign data_reversed[type][i] = data_in[`size*((i/`size) + 1) - 1 - i];
				else
					assign data_reversed[type][i] = data_in[`size*((i/`size) + 1) - 1 - (i%(`size*(i/`size)))];
			end
endgenerate

assign data_out = data_reversed[rev_type];

endmodule
