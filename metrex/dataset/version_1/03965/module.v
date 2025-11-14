



module processing_unit #(

parameter PRV_SIZE = 16,
parameter PRV_LOOP = 1,
parameter WEIGHT_WIDTH = 3,
parameter FRACTION_WIDTH = 8,
parameter REG_WIDTH = $clog2(PRV_SIZE*PRV_LOOP*3) + 8 + 1,
parameter BIAS = 0

)(

input clk_i,
input en_i,
input rst_i,
input [WEIGHT_WIDTH - 1:0] weight_i,
input	[7:0] data_i,
output reg [9:0] proc_unit_o

);

reg [9:0] product = 0;
reg [REG_WIDTH - 1:0] signed_product = 0;
reg [REG_WIDTH - 1:0] sum = 0;

wire positive_cap;
wire negative_cap;

assign positive_cap = sum[REG_WIDTH - 2 : 11] != 0;
assign negative_cap = !(sum[REG_WIDTH - 2 : 11] == {(REG_WIDTH - 12){1'b1}});

always@(*)begin

	
	
	
	
	case(weight_i[2:0])
		3'd0: product = 10'd0;
		3'd1: product = {5'd0, data_i[7:3]};
		3'd2: product = {4'd0, data_i[7:2]};
		3'd3: product = {3'd0, data_i[7:1]};
		3'd4: product = data_i[7:1] + data_i[7:2];
		3'd5: product = data_i;
		3'd6: product = data_i + data_i[7:2];
		3'd7: product = data_i + data_i[7:1];
	endcase
	
	if(!weight_i[WEIGHT_WIDTH - 1'b1] || product == 0)
		signed_product = {{(REG_WIDTH - 10){1'b0}}, product};
	else
		signed_product = {{(REG_WIDTH - 10){1'b1}},~product + 1'b1};
	
	if(positive_cap && !sum[REG_WIDTH - 1])		
		proc_unit_o = 10'b0111111111;
	else if((negative_cap || sum[11:2] == 10'b1000000000) && sum[REG_WIDTH - 1])	
		proc_unit_o = 10'b1000000001;
	else
		proc_unit_o = sum[11:2];
	
end

always@(posedge clk_i) begin
	
	if(rst_i)
		sum <= BIAS;
	else if(en_i)
		sum <= sum + signed_product;

end

endmodule
