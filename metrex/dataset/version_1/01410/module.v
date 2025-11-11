
module LCD(
    input clk,
    input rst, input en,
    input reset, input set,
    input clear,
    input off,
    input on,
    input entry_mode,
    input cursor,
    input w_char,
	 input [7:0] cursor_pos,
	 input [7:0] ascii_char,
	 output reg busy,
	 
    input int_cnt,
    output reg [15:0] limit_cnt,
    output reg en_cnt,
	 
    output reg rs,
    output reg e,
    output reg [7:0] data
    );
	 
	 reg rs_d;
	 reg [5:0] state;
	 reg [7:0] data_d; 
	 
	 localparam f_rst		= 0,
					f_idle	= 1,
					f_reset	= 2,
					f_set		= 3,
					f_clear	= 4,
					f_off		= 5,
					f_on		= 6,
					f_entry	= 7,
					f_cursor	= 8,
					f_w_char	= 9;
	 localparam res_data 	= 10;
	 localparam set_data		= 11;
	 localparam clear_data	= 12;
	 localparam off_data		= 13;
	 localparam on_data		= 14;
	 localparam entry_data	= 15;
	 localparam cursor_data	= 16;
	 localparam write_data	= 17;
	 localparam lcd_en		= 18,
					lcd_del_1	= 19,
					lcd_dis		= 20,
					lcd_del_200	= 21;
	 
	 always@(posedge clk) begin
		if(rst) state <= f_rst;
		else begin
			case(state)
			f_rst: state <= f_idle;
			
			f_idle: begin
				if(en) begin
					if(reset)				state <= f_reset;
					else if(set) 			state <= f_set;
					else if(clear)			state <= f_clear;
					else if(off) 			state <= f_off;
					else if(on) 			state <= f_on;
					else if(entry_mode) 	state <= f_entry;
					else if(cursor) 		state <= f_cursor;
					else if(w_char) 		state <= f_w_char;
					else 						state <= f_idle;
				end else state <= f_idle;
			end
			
			f_reset: state <= res_data;
			
			res_data: state <= lcd_en;
			
			lcd_en: state <= lcd_del_1;
			
			lcd_del_1: begin
				if(int_cnt)	state <= lcd_dis;
				else state <= lcd_del_1;
			end
			
			lcd_dis: state <= lcd_del_200;
			
			lcd_del_200: begin
				if(int_cnt) state <= f_idle;
				else state <= lcd_del_200;
			end						
			f_set: state <= set_data;
			
			set_data: state <= lcd_en;
			
			lcd_en: state <= lcd_del_1;
			
			lcd_del_1: begin
				if(int_cnt)	state <= lcd_dis;
				else state <= lcd_del_1;
			end
			
			lcd_dis: state <= lcd_del_200;
			
			lcd_del_200: begin
				if(int_cnt) state <= f_idle;
				else state <= lcd_del_200;
			end			
			
			f_clear: state <= clear_data;
			
			clear_data: state <= lcd_en;
			
			lcd_en: state <= lcd_del_1;
			
			lcd_del_1: begin
				if(int_cnt)	state <= lcd_dis;
				else state <= lcd_del_1;
			end
			
			lcd_dis: state <= lcd_del_200;
			
			lcd_del_200: begin
				if(int_cnt) state <= f_idle;
				else state <= lcd_del_200;
			end
			
			f_off: state <= off_data;
			
			off_data: state <= lcd_en;
			
			lcd_en: state <= lcd_del_1;
			
			lcd_del_1: begin
				if(int_cnt)	state <= lcd_dis;
				else state <= lcd_del_1;
			end
			
			lcd_dis: state <= lcd_del_200;
			
			lcd_del_200: begin
				if(int_cnt) state <= f_idle;
				else state <= lcd_del_200;
			end
			
			f_on: state <= on_data;
			
			on_data: state <= lcd_en;
			
			lcd_en: state <= lcd_del_1;
			
			lcd_del_1: begin
				if(int_cnt)	state <= lcd_dis;
				else state <= lcd_del_1;
			end
			
			lcd_dis: state <= lcd_del_200;
			
			lcd_del_200: begin
				if(int_cnt) state <= f_idle;
				else state <= lcd_del_200;
			end
			
			f_entry: state <= entry_data;
			
			entry_data: state <= lcd_en;
			
			lcd_en: state <= lcd_del_1;
			
			lcd_del_1: begin
				if(int_cnt)	state <= lcd_dis;
				else state <= lcd_del_1;
			end
			
			lcd_dis: state <= lcd_del_200;
			
			lcd_del_200: begin
				if(int_cnt) state <= f_idle;
				else state <= lcd_del_200;
			end
			
			f_cursor: state <= cursor_data;
			
			cursor_data: state <= lcd_en;
			
			lcd_en: state <= lcd_del_1;
			
			lcd_del_1: begin
				if(int_cnt)	state <= lcd_dis;
				else state <= lcd_del_1;
			end
			
			lcd_dis: state <= lcd_del_200;
			
			lcd_del_200: begin
				if(int_cnt) state <= f_idle;
				else state <= lcd_del_200;
			end
			
			f_w_char: state <= write_data;
			
			write_data: state <= lcd_en;
			
			lcd_en: state <= lcd_del_1;
			
			lcd_del_1: begin
				if(int_cnt)	state <= lcd_dis;
				else state <= lcd_del_1;
			end
			
			lcd_dis: state <= lcd_del_200;
			
			lcd_del_200: begin
				if(int_cnt) state <= f_idle;
				else state <= lcd_del_200;
			end
			
			default: state <= f_rst;
			
			endcase
		end
	 end
	 
	 always@(*) begin
		case(state)
			f_rst: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 0;
				busy			<= 1;
			end
			f_idle: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 0;
				busy			<= 0; end
			f_reset: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 0;
				busy			<= 1;
			end
			f_set: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 0;
				busy			<= 1;
			end
			f_clear: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 0;
				busy			<= 1;
			end
			f_off: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 0;
				busy			<= 1;
			end
			f_on: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 0;
				busy			<= 1;
			end
			f_entry: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 0;
				busy			<= 1;
			end
			f_cursor: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 0;
				busy			<= 1;
			end
			f_w_char: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 1;
				e				<=	0;
				data			<= 0;
				busy			<= 1;
			end
			res_data: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 8'h30;
				busy 			<= 1;
			end
			
			set_data: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 8'h38;
				busy 			<= 1;
			end
			
			clear_data: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 8'h01;
				busy 			<= 1;
			end
			
			off_data: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 8'h08;
				busy 			<= 1;
			end
			
			on_data: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 8'h0C;
				busy 			<= 1;
			end
			
			entry_data: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 8'h06;
				busy 			<= 1;
			end
			
			cursor_data: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 0;
				e				<=	0;
				data			<= 8'h80|cursor_pos; busy 			<= 1;
			end
			
			write_data: begin
				limit_cnt 	<= 0;
				en_cnt		<= 0;
				rs				<= 1;
				e				<=	0;
				data			<= ascii_char; busy 			<= 1;
			end
			lcd_en: begin
				limit_cnt 	<= 100;
				en_cnt		<= 0;
				rs				<= rs_d;
				e				<=	1;
				data			<= data_d;
				busy 			<= 1;
			end
			lcd_del_1: begin
				limit_cnt 	<= 100; en_cnt		<= 1;
				rs				<= rs_d;
				e				<=	1;
				data			<= data_d;
				busy 			<= 1;
			end
			lcd_dis: begin
				limit_cnt 	<= 20000;
				en_cnt		<= 0;
				rs				<= rs_d;
				e				<=	0;
				data			<= data_d;
				busy 			<= 1;
			end
			lcd_del_200: begin
				limit_cnt 	<= 20000; en_cnt		<= 1;
				rs				<= rs_d;
				e				<=	0;
				data			<= data_d;
				busy 			<= 1;
			end
		endcase
	 end
	 
	 always@(negedge clk) begin
		data_d <= data;
		rs_d <= rs;
	 end
	 
endmodule
