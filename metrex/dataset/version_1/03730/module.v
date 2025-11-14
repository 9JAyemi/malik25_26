




module UnorderedSet #(
	parameter DEPTH			= 16,	parameter ITER_SIZE		= 4,	parameter KEY_SIZE		= 16	) (
	input wire					clk,

	input wire					insert_en,		input wire[KEY_SIZE-1:0]	insert_key,		output reg					insert_ok = 0,	input wire					iter_inc,		input wire					iter_begin,		input wire[ITER_SIZE-1:0]	iter_in,		output reg					iter_end = 0,	output reg[ITER_SIZE-1:0]	iter_next = 0,	output reg[KEY_SIZE-1:0]	iter_key = 0,	input wire					remove_en,		input wire[ITER_SIZE-1:0]	remove_iter		);

	integer i;

	reg					slot_valid[DEPTH-1:0];
	reg[KEY_SIZE-1:0]	slot_key[DEPTH-1:0];

	initial begin
		for(i=0; i<DEPTH; i=i+1) begin
			slot_valid[i]	<= 0;
			slot_key[i]		<= 0;
		end
	end

	reg		hit = 0;

	always @(*) begin

		iter_end		<= 1;		iter_next		<= 0;

		hit				= 0;

		if(iter_begin) begin
			for(i=0; i<DEPTH; i=i+1) begin
				if(slot_valid[i] && !hit) begin
					hit			= 1;
					iter_end	<= 0;
					iter_next	<= i;
					iter_key	<= slot_key[i];
				end
			end
		end

		else if(iter_inc) begin
			for(i=0; i<DEPTH; i=i+1) begin
				if(slot_valid[i] && !hit && (i > iter_in) ) begin
					hit			= 1;
					iter_end	<= 0;
					iter_next	<= i;
					iter_key	<= slot_key[i];
				end
			end
		end

	end

	always @(posedge clk) begin

		insert_ok		= 0;

		if(insert_en) begin

			for(i=0; i<DEPTH; i=i+1) begin
				if(slot_valid[i] && (slot_key[i] == insert_key) ) begin
					insert_ok		= 1;
				end
			end

			for(i=0; i<DEPTH; i=i+1) begin
				if(!slot_valid[i] && !insert_ok) begin
					insert_ok		= 1;
					slot_valid[i]	<= 1;
					slot_key[i]		<= insert_key;
				end
			end

		end

		if(remove_en)
			slot_valid[remove_iter]	<= 0;

	end


endmodule
