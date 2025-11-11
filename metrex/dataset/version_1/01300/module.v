module acl_vector_to_stream_converter_single(
			clock, clock2x, resetn, start,
			a1, a2, dataa,
			valid_in, valid_out, stall_in, stall_out);
	parameter WIDTH = 32;
	
  input clock, clock2x, resetn, valid_in, stall_in, start;
	input [WIDTH-1:0] a1;
  input [WIDTH-1:0] a2;
  output [WIDTH-1:0] dataa;
	output valid_out;
	output stall_out;

  reg [WIDTH-1:0] a1_sr ;
  reg [WIDTH-1:0] a2_sr ;
  reg sr_in_valid ;
  wire stall_sr;
  assign stall_out = sr_in_valid;
  reg start_reg ;
  
  always@(posedge clock or negedge resetn)
  begin
    if (~resetn)
    begin
      sr_in_valid <= 1'b0;
      start_reg <= 1'b0;
      a1_sr <= {WIDTH{1'bx}};
      a2_sr <= {WIDTH{1'bx}};
    end
    else
    begin
      start_reg <= start;
      if (~stall_sr | start)
        sr_in_valid <= 1'b0;
      else if (~sr_in_valid)
        sr_in_valid <= valid_in;

      if (~sr_in_valid)
      begin
        a1_sr <= a1;
        a2_sr <= a2;
      end
    end
  end
  
  reg sel2x, sel_ref ;
	initial
	begin
		sel2x = 1'b0;
		sel_ref = 1'b0;
	end

  always@(posedge clock2x)
  begin
    sel2x <= ~sel2x;	
  end
  
	reg [WIDTH-1:0] a1_reg ;
  reg [WIDTH-1:0] a2_reg ;
  reg valid_reg ;
  wire stall_reg;
  
  assign stall_sr = valid_reg & stall_reg;
  
  always@(posedge clock or negedge resetn)
  begin
    if (~resetn)
    begin
      sel_ref <= 1'b0;
      valid_reg <= 1'b0;
      a1_reg <= {WIDTH{1'bx}};
      a2_reg <= {WIDTH{1'bx}};
    end
    else 
    begin
      sel_ref <= sel2x;
      if (start)
        valid_reg <= 1'b0;
      else if (~valid_reg | ~stall_reg)
        valid_reg <= valid_in | sr_in_valid;
        
      if (~valid_reg | ~stall_reg)
      begin
        a1_reg <= sr_in_valid ? a1_sr : a1;
        a2_reg <= sr_in_valid ? a2_sr : a2;
      end
    end
  end
  
  reg [WIDTH-1:0] shift_reg_a1 ;
  reg [WIDTH-1:0] shift_reg_a2 ;
  reg read_data ;
  reg valid_a1, valid_a2 ;
  reg start_reg_2x ;
  wire stall_shift;
  assign stall_reg = ~read_data;
  wire w;
  assign w = (sel_ref == sel2x);
  always@(posedge clock2x or negedge resetn)  
  begin
    if (~resetn)
    begin
      start_reg_2x <= 1'b0;
      valid_a1 <= 1'b0;
      valid_a2 <= 1'b0;
      read_data <= 1'b0;
      shift_reg_a1 <= {WIDTH{1'bx}};
      shift_reg_a2 <= {WIDTH{1'bx}};
    end
    else
    begin
     start_reg_2x <= start_reg;
	   if (~w)
		 begin
		   if (~valid_a1)
       begin
         valid_a1 <= valid_reg & ~start_reg_2x;
         valid_a2 <= valid_reg & ~start_reg_2x;
         shift_reg_a1 <= a1_reg;
         shift_reg_a2 <= a2_reg;
			   read_data <= valid_reg;
       end
		   else if (~stall_shift)
		   begin
		     if (~valid_a2)
         begin
           valid_a1 <= valid_reg & ~start_reg_2x;
           valid_a2 <= valid_reg & ~start_reg_2x;
           shift_reg_a1 <= a1_reg;
           shift_reg_a2 <= a2_reg;
				   read_data <= valid_reg;
         end
         else
         begin
			     valid_a1 <= valid_a2 & ~start_reg_2x;
           valid_a2 <= 1'b0;
           shift_reg_a1 <= shift_reg_a2;
           shift_reg_a2 <= {WIDTH{1'b0}};
           read_data <= 1'b0;
         end			 
		   end
       else
         read_data <= 1'b0;
		 end
		 else
		 begin
		   if (~stall_shift)
       begin
		     valid_a1 <= valid_a2 & ~start_reg_2x;
         valid_a2 <= 1'b0;
         shift_reg_a1 <= shift_reg_a2;
         shift_reg_a2 <= {WIDTH{1'b0}};
       end
       else
       begin
         valid_a1 <= valid_a1 & ~start_reg_2x;
         valid_a2 <= valid_a2 & ~start_reg_2x;
       end
     end
    end
  end
  
  assign dataa = shift_reg_a1;
  assign stall_shift = stall_in;
  assign valid_out = valid_a1;
endmodule
