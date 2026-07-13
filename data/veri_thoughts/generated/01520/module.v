module hvsync_generator(clk, vga_h_sync, vga_v_sync, inDisplayArea, CounterX, CounterY);
input clk;
output vga_h_sync, vga_v_sync;
output inDisplayArea;
output [10:0] CounterX;
output [10:0] CounterY;

integer width = 11'd800; integer height = 11'd600; integer count_dots = 11'd1056; integer count_lines = 11'd625; integer h_front_porch = 11'd16; integer h_sync_pulse = 11'd80; integer h_back_porch = 11'd160; integer v_front_porch = 11'd1; integer v_sync_pulse = 11'd3; integer v_back_porch = 11'd21; reg [10:0] CounterX;
reg [10:0] CounterY;
wire CounterXmaxed = (CounterX==count_dots);
wire CounterYmaxed = (CounterY==count_lines);

always @(posedge clk)
	if(CounterXmaxed)
		CounterX <= 0;
	else
		CounterX <= CounterX + 1;

always @(posedge clk)
	if(CounterXmaxed) 
	begin
		if (CounterYmaxed)
			CounterY <= 0;
		else
			CounterY <= CounterY + 1;
	end

reg	vga_HS, vga_VS;

always @(posedge clk)
begin
	vga_HS <= (CounterX >= (width+h_front_porch) && CounterX < (width+h_front_porch+h_sync_pulse)); 
	vga_VS <= (CounterY >= (height+v_front_porch) && CounterY < (height+v_front_porch+v_sync_pulse)); 
end

assign inDisplayArea = (CounterX < width && CounterY < height) ? 1'b1: 1'b0;	
assign vga_h_sync = vga_HS; assign vga_v_sync = vga_VS; endmodule
