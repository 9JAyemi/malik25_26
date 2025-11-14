

module sig_337p(

input [6:0] t,
output reg [7:0] y

);

reg [6:0] temp;
reg [7:0] s;
reg [26:0] p;


always@(*) begin

	if(t[6] == 1)
		temp = ~t + 1'b1;
	else
		temp = t;
	
	p[0]  =  temp[5] &  temp[2];
	p[1]  =  temp[5] &  temp[4];
	p[2]  =  temp[5];
	p[3]  =  temp[5] &  temp[3];
	p[4]  =  temp[4] & ~temp[3] & ~temp[2] & ~temp[1] & ~temp[0];
	p[5]  = ~temp[4] &  temp[3] & ~temp[2] & ~temp[1] & ~temp[0];
	p[6]  = ~temp[4] & ~temp[3] &  temp[2] &  temp[1] & ~temp[0];
	p[7]  =  temp[3] & ~temp[2] &  temp[1] & ~temp[0];
	p[8]  =  temp[4] &  temp[3] &  temp[1] &  temp[0];
	p[9]  =  temp[4] & ~temp[3] &  temp[1] &  temp[0];
	p[10] =  temp[4] &  temp[2] &  temp[1];
	p[11] = ~temp[4] &  temp[3] &  temp[1] &  temp[0];
	p[12] =  temp[3] &  temp[2] &  temp[1];
	p[13] =  temp[3] & ~temp[1] &  temp[0];
	p[14] =  temp[4] &  temp[2] &  temp[0];
	p[15] =  temp[4] & ~temp[3] & ~temp[2] & temp[1];
	p[16] = ~temp[4] & ~temp[3] & ~temp[2] & temp[1];
	p[17] = ~temp[4] &  temp[3] &  temp[2];
	p[18] =  temp[4] &  temp[3] &  temp[2];
	p[19] = ~temp[3] &  temp[2];
	p[20] = ~temp[4] &  temp[2] &  temp[1] &  temp[0];
	p[21] = ~temp[4] &  temp[2] & ~temp[1] &  temp[0];
	p[22] =  temp[4] & ~temp[3] &  temp[2] & ~temp[1];
	p[23] =  temp[4] & ~temp[2] & ~temp[1] &  temp[0];
	p[24] = ~temp[4] & ~temp[3] & ~temp[2] &  temp[0];
	p[25] =  temp[4] &  temp[3];
	p[26] =  temp[4] &  temp[3] & ~temp[2] & ~temp[0];
	
	s[7] = 1'b0;
	s[6] = 1'b1;
	s[5] = p[2] | p[4] | p[7] | p[9] | p[10] | p[11] | p[12] | p[13] |
			 p[14] | p[15] | p[17] | p[22] |  p[23] | p[25];
	s[4] = p[2] | p[4] | p[5] | p[9] | p[10] | p[14] | p[15] | p[19] |
			 p[23] | p[25];
	s[3] = p[2] | p[5] | p[10] | p[12] | p[16] | p[17] | p[20] | p[25];
	s[2] = p[2] | p[5] | p[6] | p[8] | p[11] | p[12] | p[15] | p[18] |
			 p[22] | p[24];
	s[1] = p[2] | p[5] | p[6] | p[7] | p[11] | p[20] | p[21] | p[22] |
			 p[23] | p[26];
	s[0] = p[0] | p[1] | p[3] | p[4] | p[6] | p[7] | p[9] | p[12] |
			 p[13] | p[14] | p[17] | p[21];
			 
	if(t[6] == 1)
		y = 8'b10000000 - s;
	else
		y = s;
	
	
end

endmodule
