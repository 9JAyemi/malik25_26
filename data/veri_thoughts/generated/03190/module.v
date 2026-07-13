
module number_in(
    input [31:0] num_a,
    input [31:0] num_b,
    input [31:0] result,
	 input [4:0] code,
	 input btnm,
    output reg [32:0] num_out
    );
	 
reg [31:0] new;
reg [6:0] i;
reg [1:0] state;
reg b_state;

parameter [1:0] numA = 2'b00;
parameter [1:0] numB = 2'b01;
parameter [1:0] numC = 2'b10;


initial state = 2'b00;
initial b_state = 0;

always @(*)
begin
	if(btnm)
	begin
		if(~b_state)
		begin
			b_state = 1;
			if(state == numA)		begin
				if(code > 9 && code < 15)	begin
					state = numB;
				end
			end
			else if(state == numB)		begin
				if(code == 15)	begin
					state = numC;
				end
			end
			else
			begin
				if(code == 16)	begin
					state = numA;
				end
			end
		end
	end
	else
	begin
		b_state = 0;
	end
end

always @(state)
begin
	case (state)
	numA: new = num_a;
	numB: new = num_b;
	numC: new = result;
	default: new = num_a;
	endcase
	if(new[31])
	begin
		for(i = 0; i < 32; i = i + 1)
			num_out[i] = ~new[i];
		num_out = num_out + 1'b1;
		num_out[32] = 1'b1;
	end
	else
	begin
		num_out = new;
	end
end

endmodule
