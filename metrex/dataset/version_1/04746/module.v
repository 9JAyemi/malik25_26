module vfabric_down_converter(clock, resetn, i_start,
  i_datain, i_datain_valid, o_datain_stall, 
  o_dataout, i_dataout_stall, o_dataout_valid);

parameter DATAIN_WIDTH = 32;
parameter DATAOUT_WIDTH = 8;

 input clock, resetn, i_start;
 input [DATAIN_WIDTH-1:0] i_datain;
 input i_datain_valid;
 output o_datain_stall;
 output [DATAOUT_WIDTH-1:0] o_dataout;
 input i_dataout_stall;
 output o_dataout_valid;
 
parameter s_IDLE = 3'b100;
parameter s_SEND_B1 = 3'b000;
parameter s_SEND_B2 = 3'b001;
parameter s_SEND_B3 = 3'b010;
parameter s_SEND_B4 = 3'b011;

reg [2:0] present_state, next_state;

reg [DATAIN_WIDTH-1:0] data_to_send;
wire latch_new_data;

always@(*)
begin
   case (present_state)
    s_IDLE: if (i_datain_valid)
                next_state <= s_SEND_B1;
             else
                next_state <= s_IDLE;
                
    s_SEND_B1: if (!i_dataout_stall)
                 next_state <= s_SEND_B2; 
               else 
                 next_state <= s_SEND_B1; 
    s_SEND_B2: if (!i_dataout_stall)
                 next_state <= s_SEND_B3; 
               else 
                 next_state <= s_SEND_B2; 
    s_SEND_B3: if (!i_dataout_stall)
                 next_state <= s_SEND_B4; 
               else 
                 next_state <= s_SEND_B3; 
              
    s_SEND_B4: if (!i_dataout_stall)
                 next_state <= i_datain_valid ? s_SEND_B1 : s_IDLE;
               else 
                 next_state <= s_SEND_B4;
    
    default: next_state <= 3'bxxx;
   endcase	 
end

always@(posedge clock or negedge resetn)
begin
  if (~resetn)
    data_to_send <= {DATAIN_WIDTH{1'b0}};
  else
    data_to_send <= (latch_new_data & i_datain_valid) ? 
                        i_datain : data_to_send;
end 

always@(posedge clock or negedge resetn)
begin
  if (~resetn)
     present_state <= s_IDLE;
  else
     present_state <= (i_start) ? next_state : s_IDLE;
end

  assign o_dataout = data_to_send[present_state[1:0]*DATAOUT_WIDTH +: DATAOUT_WIDTH];
  assign o_dataout_valid = ~present_state[2] & i_start;
    
  assign latch_new_data = (present_state == s_IDLE) || 
                          ((present_state == s_SEND_B4) & ~i_dataout_stall);

  assign o_datain_stall = (i_start) ? ~latch_new_data : 1'b0;
 
 
endmodule
