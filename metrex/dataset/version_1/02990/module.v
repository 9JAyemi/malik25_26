

`ifndef LED_BLINK_MOD_V_
`define LED_BLINK_MOD_V_


module led_blink #(
	parameter BLINK_ON_CLKS		= 1024,
	parameter BLINK_OFF_CLKS	= 1024,
) (
	input clk,
	input n_reset,
	input enable,
	output reg led,
);
	reg [31:0] led_on_count;
	reg [31:0] led_off_count;

	initial begin
		led <= 0;
		led_on_count <= 0;
		led_off_count <= 0;
	end

	always @(posedge clk) begin
		if (n_reset) begin
			if (led) begin
				if (led_on_count == 0) begin
					led <= 0;
					led_off_count <= BLINK_OFF_CLKS;
				end else begin
					led_on_count <= led_on_count - 1;
				end
			end else begin
				if (led_off_count == 0) begin
					if (enable) begin
						led <= 1;
						led_on_count <= BLINK_ON_CLKS;
					end
				end else begin
					led_off_count <= led_off_count - 1;
				end
			end
		end else begin
			led <= 0;
			led_on_count <= 0;
			led_off_count <= 0;
		end
	end
endmodule

`endif 
