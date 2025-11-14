module ddr3_eim_cs1(
		    input wire clk,
		    
		    input wire [63:0] ctl, 
		    input wire ctl_stb,  output wire [63:0] burst_rd,
		    input wire rd_stb,   output wire [63:0] status,

		    output wire [2:0] ddr3_rd_cmd,
		    output wire [5:0] ddr3_rd_bl,
		    output wire [29:0] ddr3_rd_adr,
		    output wire ddr3_rd_cmd_en,
		    input wire ddr3_rd_cmd_empty,
		    input wire ddr3_rd_cmd_full,

		    input wire [31:0] ddr3_rd_data,
		    input wire [6:0] ddr3_rd_count,
		    input wire ddr3_rd_empty,
		    input wire ddr3_rd_full,
		    output reg ddr3_rd_en,
		    
		    input wire reset
		    );

   reg [29:0] 		 cmd_adr;
   reg [4:0] 		 num_pkts; reg [4:0] 		 outstanding;

   reg [63:0] 		 rd_cache;

   reg 			 cmd_go;

   reg 			 reset_errors;
   reg 			 cmd_err;

   reg [7:0] 		 readcount;
   
   assign burst_rd[63:0] = rd_cache[63:0];
   
   
   assign status = {readcount,
		    3'b0,cmd_err, 
		    ddr3_rd_cmd_empty, ddr3_rd_cmd_full, ddr3_rd_empty, ddr3_rd_full, 
		    1'b0, ddr3_rd_count[6:0]};

   always @(posedge clk) begin
      if( ctl_stb ) begin
	 readcount <= 8'b0;
      end else if( rd_stb ) begin
	 readcount <= readcount + 8'b1;
      end else begin
	 readcount <= readcount;
      end
   end

   always @(posedge clk) begin
      if( ctl_stb ) begin
	 cmd_adr <= ctl[29:0];
	 num_pkts <= ctl[36:32]; end else begin
	 cmd_adr <= cmd_adr;
	 num_pkts <= num_pkts;
      end
      
      cmd_go <= ctl_stb && (ctl[36:32] != 5'b0);
   end

   assign ddr3_rd_cmd = 3'b001; assign ddr3_rd_adr = {cmd_adr[29:2],2'b00}; assign ddr3_rd_bl[5:0] = {num_pkts[4:0],1'b0} - 6'b1;
   assign ddr3_rd_cmd_en = cmd_go; parameter READ_IDLE        = 6'b1 << 0;
   parameter READ_PENDING     = 6'b1 << 1;
   parameter READ_FETCH       = 6'b1 << 2;
   parameter READ_UPDATE_LSB  = 6'b1 << 3;
   parameter READ_UPDATE_MSB  = 6'b1 << 4;
   parameter READ_WAIT        = 6'b1 << 5;

   parameter READ_nSTATES = 6;
   reg [(READ_nSTATES - 1):0] 		 cstate;
   reg [(READ_nSTATES - 1):0] 		 nstate;

   always @(posedge clk) begin
      cstate <= nstate;
   end

   always @(*) begin
      case(cstate)
	READ_IDLE: begin
	   if( cmd_go ) begin
	      nstate <= READ_PENDING;
	   end else begin
	      nstate <= READ_IDLE;
	   end
	end
	READ_PENDING: begin
	   if( outstanding != 5'b0 ) begin
	      if( ddr3_rd_count[6:0] < 7'b10 ) begin
		 nstate <= READ_PENDING;
	      end else begin
		 nstate <= READ_FETCH;
	      end
	   end else begin
	      nstate <= READ_IDLE;
	   end
	end READ_FETCH: begin
	   nstate <= READ_UPDATE_LSB;
	end
	READ_UPDATE_LSB: begin
	   nstate <= READ_UPDATE_MSB;
	end
	READ_UPDATE_MSB: begin
	   nstate <= READ_WAIT;
	end
	READ_WAIT: begin
	   if( rd_stb ) begin  nstate <= READ_PENDING;
	   end else begin
	      nstate <= READ_WAIT;
	   end
	end
	default: begin
	   nstate <= READ_IDLE;
	end
      endcase end always @(posedge clk) begin
      case(cstate)
	READ_IDLE: begin
	   outstanding[4:0] <= num_pkts[4:0];
	   rd_cache <= rd_cache;
	   if( ddr3_rd_count[6:0] > 7'b0 ) begin
	      ddr3_rd_en <= 1'b1; end else begin
	      ddr3_rd_en <= 1'b0;
	   end
	end
	READ_PENDING: begin
	   outstanding <= outstanding;
	   rd_cache <= rd_cache;
	   ddr3_rd_en <= 1'b0;
	end
	READ_FETCH: begin
	   outstanding <= outstanding;
	   rd_cache <= rd_cache;
	   ddr3_rd_en <= 1'b1;
	end
	READ_UPDATE_LSB: begin
	   outstanding <= outstanding;
	   rd_cache[63:0] <= {rd_cache[63:32],ddr3_rd_data[31:0]};
	   ddr3_rd_en <= 1'b1;
	end
	READ_UPDATE_MSB: begin
	   outstanding <= outstanding - 5'b1;
	   rd_cache[63:0] <= {ddr3_rd_data[31:0],rd_cache[31:0]};
ddr3_rd_en <= 1'b0;
	end
	READ_WAIT: begin
	   outstanding <= outstanding;
	   rd_cache <= rd_cache;
	   ddr3_rd_en <= 1'b0;
	end
	default: begin
	   outstanding <= outstanding;
	   rd_cache <= rd_cache;
	   ddr3_rd_en <= 1'b0;
	end
      endcase end
   
   
   always @(posedge clk) begin
      reset_errors <= ctl[63];
      if( reset_errors ) begin
	 cmd_err <= 1'b0;
      end else begin
	 if( cmd_go && ddr3_rd_cmd_full ) begin
	    cmd_err <= 1'b1;
	 end else begin
	    cmd_err <= cmd_err;
	 end
      end
   end endmodule 