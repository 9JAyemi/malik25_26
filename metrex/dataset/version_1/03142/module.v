
module contador_AD_HH_2dig
(
input wire clk, 
input wire reset,
input wire [3:0]en_count,
input wire enUP,
input wire enDOWN,
output wire [7:0] data_HH);                             


localparam N = 5; reg [N-1:0] q_act, q_next;
wire [N-1:0] count_data;
reg [3:0] digit1, digit0;

always@(posedge clk, posedge reset)
begin	
	
	if(reset)
	begin
		q_act <= 5'b0;
	end
	
	else
	begin
		q_act <= q_next;
	end
end


always@*
begin

	if (en_count == 3)
	begin
		if (enUP)
		begin
			if (q_act >= 5'd23) q_next = 5'd0;
			else q_next = q_act + 5'd1;
		end
		
		else if (enDOWN)
		begin
			if (q_act == 5'd0) q_next = 5'd23;
			else q_next = q_act - 5'd1;
		end
		else q_next = q_act;
	end
	else q_next = q_act;
	
end

assign count_data = q_act;

always@*
begin
	case(count_data)
		5'd0: begin digit1 = 4'b0000; digit0 = 4'b0000; end
		5'd1: begin digit1 = 4'b0000; digit0 = 4'b0001; end
		5'd2: begin digit1 = 4'b0000; digit0 = 4'b0010; end
		5'd3: begin digit1 = 4'b0000; digit0 = 4'b0011; end
		5'd4: begin digit1 = 4'b0000; digit0 = 4'b0100; end
		5'd5: begin digit1 = 4'b0000; digit0 = 4'b0101; end
		5'd6: begin digit1 = 4'b0000; digit0 = 4'b0110; end
		5'd7: begin digit1 = 4'b0000; digit0 = 4'b0111; end
		5'd8: begin digit1 = 4'b0000; digit0 = 4'b1000; end
		5'd9: begin digit1 = 4'b0000; digit0 = 4'b1001; end

		5'd10: begin digit1 = 4'b0001; digit0 = 4'b0000; end
		5'd11: begin digit1 = 4'b0001; digit0 = 4'b0001; end
		5'd12: begin digit1 = 4'b0001; digit0 = 4'b0010; end
		5'd13: begin digit1 = 4'b0001; digit0 = 4'b0011; end
		5'd14: begin digit1 = 4'b0001; digit0 = 4'b0100; end
		5'd15: begin digit1 = 4'b0001; digit0 = 4'b0101; end
		5'd16: begin digit1 = 4'b0001; digit0 = 4'b0110; end
		5'd17: begin digit1 = 4'b0001; digit0 = 4'b0111; end
		5'd18: begin digit1 = 4'b0001; digit0 = 4'b1000; end
		5'd19: begin digit1 = 4'b0001; digit0 = 4'b1001; end

		5'd20: begin digit1 = 4'b0010; digit0 = 4'b0000; end
		5'd21: begin digit1 = 4'b0010; digit0 = 4'b0001; end
		5'd22: begin digit1 = 4'b0010; digit0 = 4'b0010; end
		5'd23: begin digit1 = 4'b0010; digit0 = 4'b0011; end
		default:  begin digit1 = 0; digit0 = 0; end
	endcase	
end

assign data_HH = {digit1,digit0};

endmodule
