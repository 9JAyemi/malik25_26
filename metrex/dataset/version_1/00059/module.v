

module des_smline_3d
	(
	input		de_clk,
	input		de_rstn,
	input		load_actv_3d,
	input 		line_actv_3d,
	input 		nlst_2,
	input [15:0]	cpx0,
	input [15:0]	cpy0,
	input [15:0]	cpx1,
	input [15:0]	cpy1,
	input 		pipe_busy,

	output reg			l_pixreq,
	output reg			l_last_pixel,
	output reg			l_pc_msk_last,
	output reg			l_incpat,	output reg signed	[15:0]	cpx,		output reg signed	[15:0]	cpy,		output reg			l_active	);


wire 		eol;
wire [2:0]	dir;
wire		eneg;
wire		eeqz;


reg		dir_maj;
reg [1:0]	dir_min;
reg		l_delta_x;
reg		l_delta_y;

reg signed [15:0] pline_x;
reg signed [15:0] pline_y;
reg signed [15:0] delta_x;
reg signed [15:0] delta_y;
reg signed [15:0] out_x;
reg signed [15:0] out_y;
reg signed [15:0] error_reg;
reg signed [15:0] einc_x;
reg signed [15:0] einc_y;

reg	ld_error;
reg	l_einc_x;
reg	l_einc_y;
reg	inc_err;
reg	rst_err;
reg	l_chgx;
reg	l_chgy;
wire	l_rht;
wire	l_dwn;

reg	l_ldmaj;
reg	l_ldmin;

reg		ld_itr;
reg		dec_itr;
reg [15:0]	itr_count;
reg		l_active_a;
reg		go_line_1;
reg		go_line;

always @(posedge de_clk, negedge de_rstn) begin
	if(!de_rstn) begin
		go_line   <= 1'b0;
		go_line_1 <= 1'b0;
		l_active <= 1'b0;
		pline_x <= 16'h0;
		pline_y <= 16'h0;

		cpx 	<= 16'h0;
		cpy 	<= 16'h0;
		delta_x <= 16'h0;
		delta_y <= 16'h0;
		dir_maj <= 1'b0;
		dir_min <= 2'b00;
		error_reg <= 16'h0;
		einc_x    <= 16'h0;
		einc_y    <= 16'h0;

		itr_count <= 16'h0;
	end 
	else begin
		go_line   <= (line_actv_3d & go_line_1);
		go_line_1 <= load_actv_3d;

		l_active <= l_active_a;

		pline_x <= out_x;
		pline_y <= out_y;

		if(l_delta_x) delta_x <= out_x;
		if(l_delta_y) delta_y <= out_y;

      		if(go_line) cpx <= cpx0;
		else if(l_rht & l_chgx) cpx <= cpx + 16'h1;
		else if(l_chgx)  cpx <= cpx - 16'h1;

      		if(go_line) cpy <= cpy0;
		else if(l_dwn & l_chgy) cpy <= cpy + 16'h1;
		else if(l_chgy)  cpy <= cpy - 16'h1;

		if(l_ldmin)    dir_min <= {out_y[15], out_x[15]};
		if(l_ldmaj)    dir_maj <= out_x[15];
		if(l_einc_x)   einc_x <= out_x;
		if(l_einc_y)   einc_y <= out_y;

		if(ld_error)   error_reg <= out_x;
		else if(inc_err)   error_reg <= error_reg + einc_y;
		else if(rst_err)   error_reg <= error_reg - einc_x;

		if(ld_itr)   	 itr_count <= delta_x;
		else if(dec_itr) itr_count <= itr_count - 16'h1;

	end
end

assign eneg = error_reg[15];
assign eeqz = ~|error_reg;

assign eol = ~|itr_count;

assign dir = {dir_maj, dir_min};






parameter
        LWAIT		= 4'h0,
	L1		= 4'h1,
	L2		= 4'h2,
	L3		= 4'h3,
	L4		= 4'h4,
	L5		= 4'h5,
	L6		= 4'h6,
        L7		= 4'h7,
	L8		= 4'h8,
	L9		= 4'h9,
	LIDLE1		= 4'hA;
reg [3:0]	l_cs, l_ns;

parameter
		                
		                
		                
		  o0=3'b000,	
		  o1=3'b001,	
		  o2=3'b010,	
		  o3=3'b011,	
		  o4=3'b100,	
		  o5=3'b101,	
		  o6=3'b110,	
		  o7=3'b111;	

always @(posedge de_clk, negedge de_rstn)
	if(!de_rstn) l_cs	<= LWAIT;
	else 	     l_cs	<= l_ns;

  assign l_rht = ((dir==o0) || (dir==o2) || (dir==o4) || (dir==o6));
  assign l_dwn = ((dir==o0) || (dir==o1) || (dir==o4) || (dir==o5));
  
  always @* begin
		l_active_a 	= 1'b1;
    		l_ldmaj      	= 1'b0;
    		l_ldmin      	= 1'b0;
    		l_delta_x 	= 1'b0;
    		l_delta_y 	= 1'b0;
    		l_incpat     	= 1'b0;
    		inc_err      	= 1'b0;
    		rst_err      	= 1'b0;
    		l_einc_x 	= 1'b0;
    		l_einc_y 	= 1'b0;
    		ld_error     	= 1'b0;
    		out_x 	 	= 16'h0;
    		out_y 	 	= 16'h0;
    		ld_itr     	= 1'b0;
    		dec_itr     	= 1'b0;

    		l_pc_msk_last 	= 1'b0;
    		l_last_pixel  	= 1'b0;
    		l_chgx        	= 1'b0;
    		l_chgy        	= 1'b0;
    		l_pixreq      	= 1'b0;
    
    case(l_cs)
      LWAIT: if(go_line) begin	
	      		out_x   = cpx1 - cpx0;
			out_y   = cpy1 - cpy0;
			l_ldmin = 1'b1;
			l_ns	= L1;
			end
	else begin
		l_ns= LWAIT;
		l_active_a = 1'b0;
	end

      L1:	begin	out_x = (pline_x[15]) ? ~pline_x + 16'h1 : pline_x;
			out_y = (pline_y[15]) ? ~pline_y + 16'h1 : pline_y;
			l_delta_x = 1'b1;
			l_delta_y = 1'b1;
			l_ns = L2;
			end

      L2:	begin
			l_ns     = L3;
			l_ldmaj  = 1'b1;
			out_x = pline_x - pline_y; 	end

      L3:	l_ns = L4;
      L4:	begin
			l_ns = L5;
			if(dir[2]) begin
				out_x = delta_y;
				out_y = delta_x;
				l_delta_x = 1'b1;
				l_delta_y = 1'b1;
			end
			else begin
				out_x = delta_x;
				out_y = delta_y;
			end
      end
      
      L5:	begin
			l_ns =L6;
			out_x = (pline_x << 1) - (pline_y << 1);
			out_y = (pline_y << 1);
			l_einc_x = 1'b1;
			l_einc_y = 1'b1;
    			ld_itr   = 1'b1;
      		end
      
      L6:	begin
			l_ns=L7;
			ld_error = 1'b1;
			out_x = (~delta_x + 16'h1) + (delta_y << 1);
			end
      
      L7:	begin
	if(!pipe_busy) begin
			out_x = pline_x;
	  		out_y = pline_y;
	  		l_ns = L9;
		end
	else begin
		l_ns = L8;
		end
      end

      L8:	begin
	if(eol && nlst_2) begin
	  		l_ns = LIDLE1;
	  		l_pixreq = 1'b1;
	  		l_last_pixel  =  1'b1;
	  		l_pc_msk_last = 1'b1;
	  		end
	else if(!pipe_busy && eol && !nlst_2) begin
	  		l_ns = LIDLE1;
	  		l_incpat = 1'b1;
	  		end
	else if(!pipe_busy && !eol) begin
    			dec_itr  = 1'b1;
	  		l_incpat = 1'b1;
	  		l_ns = L8;
	    		if(!pipe_busy && (dir==o1 || dir==o3 || dir==o5 || dir==o7) && !eneg && !eeqz)	rst_err = 1;
	    		else if(!pipe_busy && (dir==o0 || dir==o2 || dir==o4 || dir==o6) && !eneg)	rst_err = 1;
			else if(!pipe_busy) begin
				inc_err = 1;	end
	end
	else 	begin

	  		l_ns = L8;
	end

	if(!pipe_busy) begin	
        	if(eol && !nlst_2) begin
	  		l_pixreq = 1'b1;
	  		l_last_pixel  =  1'b1;
        	end 
        	else if(!eol)l_pixreq = 1'b1;
		
        	if(!eol && (dir==o1 || dir==o3 || dir==o5 || dir==o7) && !eneg && !eeqz)l_chgx = 1'b1;
        	else if(!eol && (dir==o0 || dir==o2 || dir==o4 || dir==o6) && !eneg)       l_chgx = 1'b1;
        	else if(!eol && (dir==o0 || dir==o1 || dir==o2 || dir==o3))
          		l_chgx = 1'b1;
		
        	if(!eol && (dir==o1 || dir==o3 || dir==o5 || dir==o7) && !eneg && !eeqz)l_chgy = 1'b1;
        	else if(!eol && (dir==o0 || dir==o2 || dir==o4 || dir==o6) && !eneg)         l_chgy = 1'b1;
        	else if(!eol && (dir==o4 || dir==o5 || dir==o6 || dir==o7))
          		l_chgy = 1'b1;
	end
      end

      L9:	begin
	l_ns=L8;
	out_x = pline_x;
	out_y = pline_y;
      end
      LIDLE1:	begin 
	l_ns = LWAIT;
      end
    endcase
    
  end

endmodule
