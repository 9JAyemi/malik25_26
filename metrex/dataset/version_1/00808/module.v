
module FxP_ABS_Function
#(
	parameter DATA_WIDTH = 16
)
(
	input   [DATA_WIDTH-1:0] DATA_IN,
	output  [DATA_WIDTH-1:0] DATA_ABS
);

	assign DATA_ABS = DATA_IN[DATA_WIDTH-1] ? ~DATA_IN + 1'b1 : DATA_IN;

endmodule
