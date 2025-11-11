module acl_fp_convert_to_half(clock, resetn, dataa, result, valid_in, valid_out, stall_in, stall_out, enable);
  parameter HIGH_CAPACITY = 1;
  parameter ROUNDING_MODE = 0;
    input clock, resetn;
  input [31:0] dataa;
  output [15:0] result;
  input valid_in, stall_in, enable;
  output valid_out, stall_out;
    
  wire c1_enable;
  reg c1_valid;
  wire c1_stall;
  wire c2_enable;
  reg c2_valid;
  wire c2_stall;  
  
  reg [4:0] c1_exponent;
  reg [13:0] c1_mantissa;
  reg c1_sign;
  
  assign c1_enable = (HIGH_CAPACITY == 1) ? (~c1_valid | ~c1_stall) : enable;
  assign stall_out = c1_valid & c1_stall;
  
  always@(posedge clock or negedge resetn)
  begin
    if(~resetn)
    begin
      c1_valid <= 1'b0;
      c1_exponent <= 5'dx;
      c1_mantissa <= 14'dx;
      c1_sign <= 1'bx;
    end
    else if (c1_enable)
    begin
      c1_valid <= valid_in;
      c1_sign <= dataa[31];
      if ({1'b0, dataa[30:23]} <= 9'd112)
      begin
        case(dataa[30:23])
          8'h70 : c1_mantissa <= {2'd1, dataa[22:12],|dataa[11:0]}; 8'h6F : c1_mantissa <= {3'd1, dataa[22:13],|dataa[12:0]};
          8'h6E : c1_mantissa <= {4'd1, dataa[22:14],|dataa[13:0]};
          8'h6D : c1_mantissa <= {5'd1, dataa[22:15],|dataa[14:0]};
          8'h6C : c1_mantissa <= {6'd1, dataa[22:16],|dataa[15:0]};
          8'h6B : c1_mantissa <= {7'd1, dataa[22:17],|dataa[16:0]};
          8'h6A : c1_mantissa <= {8'd1, dataa[22:18],|dataa[17:0]};
          8'h69 : c1_mantissa <= {9'd1, dataa[22:19],|dataa[18:0]};
          8'h68 : c1_mantissa <= {10'd1, dataa[22:20],|dataa[19:0]};
          8'h67 : c1_mantissa <= {11'd1, dataa[22:21],|dataa[20:0]};
          8'h66 : c1_mantissa <= {12'd1, dataa[22],|dataa[21:0]}; default : c1_mantissa <= 14'd0;
        endcase
        c1_exponent <= 5'd0;
      end
      else if (&dataa[30:23])
      begin
        c1_exponent <= 5'h1f;
        c1_mantissa <= {1'b1, |dataa[22:0], 12'd0};
      end
      else if ({1'b0, dataa[30:23]} > 9'h08e)
      begin
        if ((ROUNDING_MODE == 0) || (ROUNDING_MODE == 1))
        begin
          c1_exponent <= 5'h1f;
          c1_mantissa <= 14'd0;
        end
        else if (ROUNDING_MODE == 2)
        begin
          c1_exponent <= 5'h1e;
          c1_mantissa <= 14'h3ff8;
        end
        else if (ROUNDING_MODE == 3)
        begin
          c1_exponent <= dataa[31] ? (5'h1e) : (5'h1f);
          c1_mantissa <= dataa[31] ? 14'h3ff8 : 14'd0;
        end
        else if (ROUNDING_MODE == 4)
        begin
          c1_exponent <= (~dataa[31]) ? (5'h1e) : (5'h1f);
          c1_mantissa <= (~dataa[31]) ? 14'h3ff8 : 14'd0;
        end
      end
      else
      begin
        c1_exponent <= dataa[30:23] - 8'h70;
        c1_mantissa <= {1'b1, dataa[22:11],|dataa[10:0]};
      end
    end
  end
  
  reg [4:0] c2_exponent;
  reg [9:0] c2_mantissa;
  reg c2_sign;
  reg [11:0] c2_temp_mantissa;
  
  assign c2_enable = (HIGH_CAPACITY == 1) ? (~c2_valid | ~c2_stall) : enable;
  assign c1_stall = c2_valid & c2_stall;
  
  always@(*)
  begin
    case (ROUNDING_MODE)
    4: begin
      if ((|c1_mantissa[2:0]) & c1_sign)
        c2_temp_mantissa <= {1'b0, c1_mantissa[13:3]} + 1'b1;
      else
        c2_temp_mantissa <= {1'b0, c1_mantissa[13:3]};
    end
    3: begin
      if ((|c1_mantissa[2:0]) & ~c1_sign)
        c2_temp_mantissa <= {1'b0, c1_mantissa[13:3]} + 1'b1;
      else
        c2_temp_mantissa <= {1'b0, c1_mantissa[13:3]};
    end
    2: begin
      c2_temp_mantissa <= {1'b0, c1_mantissa[13:3]};
    end
    1: begin
      c2_temp_mantissa <= {1'b0, c1_mantissa[13:3]} + {1'b0, c1_mantissa[2]};
    end
    
    default: begin
      if ((c1_mantissa[3:0] == 4'b1100) || ({1'b0, c1_mantissa[2:0]} > 4'h4))
        c2_temp_mantissa <= {1'b0, c1_mantissa[13:3]} + 1'b1;
      else
        c2_temp_mantissa <= {1'b0, c1_mantissa[13:3]};
    end
    endcase  
  end
  
  always@(posedge clock or negedge resetn)
  begin
    if(~resetn)
    begin
      c2_valid <= 1'b0;
      c2_exponent <= 5'dx;
      c2_mantissa <= 10'dx;
      c2_sign <= 1'bx;
    end
    else if (c2_enable)
    begin
      c2_valid <= c1_valid;
      c2_sign <= c1_sign;
      if (c2_temp_mantissa[11])
      begin
        c2_exponent <= c1_exponent + 1'b1;
        c2_mantissa <= c2_temp_mantissa[10:1];
      end
      else
      begin
        c2_exponent <= c1_exponent + {1'b0, (c2_temp_mantissa[10] & (~|c1_exponent))};
        c2_mantissa <= c2_temp_mantissa[9:0];
      end
    end
  end  
  
  assign result = {c2_sign, c2_exponent, c2_mantissa};
  assign valid_out = c2_valid;
  assign c2_stall = stall_in;
  
 endmodule
 
  
