
module r_DEVICE_CAPABILITIES_2_HIGH(output reg [7:0] reg_0x2A, input wire reset, input wire wenb, input wire [7:0] in_data, input wire clk, input wire select);
	reg [7:0] reg_0x25;
	
	r_DEVICE_CAPABILITIES_1_HIGH r_device_capabilities_1_high_inst( .reg_0x25(reg_0x25), .reset(reset), .wenb(wenb), .in_data(in_data), .clk(clk));
	
	always@(posedge clk)
	begin
		if(reset==1)
			reg_0x2A<=8'h00;
		else if(select==0)
		begin
			if(wenb==0)
				reg_0x2A<=in_data;
		end
		else
		begin
			if(wenb==0)
				reg_0x2A<=reg_0x25;
		end
	end
endmodule
module r_DEVICE_CAPABILITIES_1_HIGH(output reg [7:0] reg_0x25, input wire reset, input wire wenb, input wire [7:0] in_data, input wire clk);

	always@(posedge clk)
	begin
		if(reset==1)
			reg_0x25<=8'h00;
		else if(wenb==0)
			reg_0x25<=in_data;
	end
endmodule