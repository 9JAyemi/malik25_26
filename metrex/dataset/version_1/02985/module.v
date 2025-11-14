

module non_posted_pkt_slicer(
    input         clk,
    input         rst,
    input         transferstart,	 
    input         rd_dma_start,
    input [31:0]  dmarad,
    input [31:0]  dmarxs,
    input [63:0]  dmaras,
    input [2:0]   read_req_size,input         rd_TX_des_start_one,
	 input [63:0]  TX_des_addr,
	 output reg    isDes,
    input         ack,
    output reg    go,
    output reg [31:0] dmarad_reg,
    output reg [63:0] dmaras_reg,
    output [9:0]  length
);
    
    localparam IDLE = 4'h0; 
    localparam IDLE_WAIT = 4'h1;
    localparam START = 4'h2; 
    localparam NORMAL = 4'h3; 
    localparam CROSS = 4'h4; 
    localparam LAST = 4'h5;
    localparam WAIT_FOR_ACK = 4'h6;
    localparam REGISTER_DMA_REG = 4'h7;
	 localparam START_TX_DES_REQ = 4'h8;

        reg [31:0]  dmarad_new,dmarad_reg2;
        reg [31:0]  dmarxs_new,dmarxs_reg,
                                                        dmarxs_reg2;
        reg [63:0]  dmaras_new,dmaras_reg2;
    wire [31:0] dmarad_add, dmarad_term;
    wire [31:0] dmarxs_sub, dmarxs_term;
    wire [63:0] dmaras_add, dmaras_term;
    reg [3:0]   state;
    reg         update_dma_reg;
    reg         stay_2x; reg [12:0]   length_byte;
    wire [63:0] dmaras_temp;
    wire        four_kb_cross;     reg [12:0] four_kb_xfer, 
                                                       four_kb_xfer2;
    wire        less_than_rrs;wire [12:0] read_req_size_bytes;
    reg         last_flag;
    reg   rst_reg;

    always@(posedge clk) rst_reg <= rst;
 

assign read_req_size_bytes =13'h0001<<(read_req_size+7);

assign dmaras_temp = dmaras_reg + read_req_size_bytes;
assign four_kb_cross = (dmaras_temp[12] == dmaras_reg2[12]) ? 1'b0 : 1'b1;

assign less_than_rrs = (dmarxs_reg <= read_req_size_bytes) ? 1'b1 : 1'b0; 

always@(posedge clk)begin
    four_kb_xfer[12:0] = 13'h1000 - dmaras_reg[11:0]; 
    four_kb_xfer2[12:0] = 13'h1000 - dmaras_reg2[11:0]; 
end

always @ (posedge clk) begin
  if (rst_reg | (~transferstart)) begin
      state <= IDLE;
      update_dma_reg <= 0;
      stay_2x <= 1'b0;
      go <= 0;
      last_flag <= 1'b0;
  end else begin
      case (state)
        IDLE : begin
           update_dma_reg <= 0;
           stay_2x <= 1'b0;
           go <= 0;
           last_flag <= 1'b0;
           if(rd_dma_start) 
             state <= IDLE_WAIT;
           else if(rd_TX_des_start_one)    state <= START_TX_DES_REQ;    else                            
             state <= IDLE;
           end
         IDLE_WAIT: begin state <= START;
         end
			
			START_TX_DES_REQ: begin
			  go <= 1;  if(stay_2x == 1'b0)begin
              state <= START_TX_DES_REQ;
              stay_2x <= 1'b1;
           end else begin
			     last_flag <= 1;
              stay_2x <= 1'b0; 
              state <= WAIT_FOR_ACK;
           end
			end
			
         START : begin        update_dma_reg <= 0;
           stay_2x <= 1'b0;
           go <= 0;
           case ({four_kb_cross, less_than_rrs})
               2'b00:
                  state <= NORMAL;
               2'b01:
                  state <= LAST;
               2'b10:
                  state <= CROSS;
               2'b11:if(dmarxs_reg > four_kb_xfer)
                  state <= CROSS;
                 else
                  state <= LAST;
            endcase      
         end
   
         NORMAL : begin go <= 1;  if(stay_2x == 1'b0)begin
              state <= NORMAL;
              stay_2x <= 1'b1;
           end else begin
              stay_2x <= 1'b0; 
              state <= WAIT_FOR_ACK;
           end
          end
         CROSS : begin go <= 1;           
           if(stay_2x == 1'b0)begin
              state <= CROSS;
              stay_2x <= 1'b1;
           end else begin
              stay_2x <= 1'b0; 
              state <= WAIT_FOR_ACK;
           end
         end
         LAST : begin go <= 1;          
           last_flag <= 1'b1;           
           if(stay_2x == 1'b0)begin
              state <= LAST;
              stay_2x <= 1'b1;
           end else begin
              stay_2x <= 1'b0; 
              state <= WAIT_FOR_ACK;
           end
          end

         WAIT_FOR_ACK : begin
           if(ack)begin
             update_dma_reg <= 1'b1;
             go <= 1'b0;
             if(last_flag)begin
               state <= IDLE;
             end else begin
               state <= REGISTER_DMA_REG;
             end
           end else begin 
             update_dma_reg <= 1'b0;
             go <= 1'b1;
             state <= WAIT_FOR_ACK;
           end
         end

         REGISTER_DMA_REG: begin
           update_dma_reg <= 1'b0;
           state <= IDLE_WAIT;
         end

         default : begin
           update_dma_reg <= 0;
           go <= 0;
           state <= IDLE;
         end
      endcase   
     end
    end

assign dmarad_term = (state == NORMAL) ? read_req_size_bytes : 
                     (state == CROSS)  ? four_kb_xfer : 
                     (state == LAST)   ? dmarxs_reg : 
                                         read_req_size_bytes;
                                                                                assign dmarad_add = dmarad_reg2 + dmarad_term;

assign dmaras_term = (state == NORMAL) ? read_req_size_bytes : 
                     (state == CROSS)  ? four_kb_xfer2 : 
                     (state == LAST)   ? dmarxs_reg : 
                                         read_req_size_bytes;
                                                                                assign dmaras_add = dmaras_reg2 + dmaras_term;

assign dmarxs_term = (state == NORMAL) ? read_req_size_bytes : 
                     (state == CROSS)  ? four_kb_xfer2 : 
                     (state == LAST)   ? dmarxs_reg : 
                                         read_req_size_bytes;
assign dmarxs_sub = dmarxs_reg2 - dmarxs_term;

always@(posedge clk)begin
   if(stay_2x)begin
           dmarad_new <= dmarad_add;
           dmaras_new <= dmaras_add;
           dmarxs_new <= dmarxs_sub;
   end
end

always@(posedge clk)begin
   if(rst_reg)begin
      dmarad_reg <= 32'h0000_0000;
      dmarxs_reg <= 32'h0000_0000;
      dmaras_reg <= 64'h0000_0000_0000_0000;
      dmarad_reg2 <= 32'h0000_0000;
      dmarxs_reg2 <= 32'h0000_0000;
      dmaras_reg2 <= 64'h0000_0000_0000_0000;      
   end else if(rd_dma_start)begin
      dmarad_reg <= dmarad;
      dmarxs_reg <= dmarxs;
      dmaras_reg <= dmaras;
      dmarad_reg2 <= dmarad;
      dmarxs_reg2 <= dmarxs;
      dmaras_reg2 <= dmaras;      
   end else if(update_dma_reg)begin
      dmarad_reg <= dmarad_new; 
      dmarxs_reg <= dmarxs_new;
      dmaras_reg <= dmaras_new;   
      dmarad_reg2 <= dmarad_new; 
      dmarxs_reg2 <= dmarxs_new;
      dmaras_reg2 <= dmaras_new;      
   end else if(rd_TX_des_start_one)begin    dmaras_reg <= TX_des_addr;            end
end   

always@(posedge clk)begin
   if(rst_reg)
      length_byte[12:0] <= 0;
   else if(state == NORMAL)
      length_byte[12:0] <= read_req_size_bytes[12:0];
   else if (state == LAST)
      length_byte[12:0] <= dmarxs_reg2[12:0];
   else if (state == CROSS)
      length_byte[12:0] <= four_kb_xfer2[12:0];
   else if (state == START_TX_DES_REQ)      length_byte[12:0] <= 13'h0020;        else
      length_byte <= length_byte;
end

assign length[9:0] = length_byte[11:2];  

always@ (posedge clk)begin
   if(rst_reg)
	   isDes <= 0;
	else if ((state == NORMAL) | (state == LAST) | (state == CROSS))
	   isDes <= 0;
	else if (state == START_TX_DES_REQ)
	   isDes <= 1;
	else
	   isDes <= isDes;
end 

endmodule
