
module ps2_kbd (
                clk, 
                clrn, 
                ps2_clk, 
                ps2_data, 
                rdn, 
                data, 
                ready, 
                overflow
                );

	input              	clk, clrn;          input              	ps2_clk, ps2_data;  input              	rdn;                output     	[ 7: 0] data;               output             	ready;              output reg         	overflow;           reg        	[ 3: 0] count;              reg        	[ 9: 0] buffer;             reg        	[ 7: 0] fifoo[7:0];         reg        	[ 2: 0] w_ptr, r_ptr;       reg        	[ 2: 0] ps2_clk_sync;       integer    	        i;

	initial begin 
        count    <= 0;                     	w_ptr    <= 0;                     	r_ptr    <= 0;                     	overflow <= 0;                     	for(i = 0; i < 8; i = i + 1) fifoo[i]=0;
	end


	always @ (posedge clk) begin                       ps2_clk_sync <= {ps2_clk_sync[1:0],ps2_clk};       end                                                    wire sampling = ps2_clk_sync[2] & ~ps2_clk_sync[1];    reg [1:0] rdn_falling;
	
	always @ (posedge clk) begin
		rdn_falling <= {rdn_falling[0],rdn};
		if (clrn == 0) begin
			count 		<= 0;
			w_ptr 		<= 0;
			r_ptr 		<= 0;
			overflow 	<= 0;
		end else if (sampling) begin
			if (count == 4'd10) begin                  if ((buffer[0] == 0) && (ps2_data) && (^buffer[9:1])) begin fifoo[w_ptr] <= buffer[8:1];       w_ptr <= w_ptr + 3'b1;             overflow <= overflow | (r_ptr == (w_ptr + 3'b1));
				end
			count <= 0;                                end else begin                             buffer[count]   <= ps2_data;           count           <= count + 3'b1;       end
		end

		if ((rdn_falling == 2'b01) && ready) begin     r_ptr    <= r_ptr + 3'b1;                  overflow <= 0;                             end
	end

	assign ready   = (w_ptr != r_ptr);                 assign data    = fifoo[r_ptr];                     endmodule

