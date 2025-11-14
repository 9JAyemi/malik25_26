
module CRC_serial_m_lfs_XOR
#(
	parameter	HASH_LENGTH = 64
)
(
	i_message     ,  
	i_cur_parity  ,  
	o_next_parity
);
	input						i_message    ;
	input	[HASH_LENGTH-1:0]	i_cur_parity  ;
	output	[HASH_LENGTH-1:0]	o_next_parity ;
	
	localparam	[0:64]	HASH_VALUE	=	65'b11001001011011000101011110010101110101111000011100001111010000101;
	
	wire	w_feedback_term;
	
	assign	w_feedback_term	=	i_message ^ i_cur_parity[HASH_LENGTH-1];
	
	assign	o_next_parity[0]	=	w_feedback_term;
	
	genvar	i;
	generate
		for (i=1; i<HASH_LENGTH; i=i+1)
		begin: linear_function
			if (HASH_VALUE[i] == 1)
				assign	o_next_parity[i] = i_cur_parity[i-1] ^ w_feedback_term;
			else
				assign	o_next_parity[i] = i_cur_parity[i-1];
		end
	endgenerate
	
endmodule