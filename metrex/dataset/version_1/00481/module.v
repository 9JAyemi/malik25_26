
module dual_port_memory (
    input wire clk,  // 28MHz
    input wire [20:0] a1,
    input wire [20:0] a2,
    input wire oe1_n,
    input wire oe2_n,
    input wire we1_n,
    input wire we2_n,
    input wire [7:0] din1,
    input wire [7:0] din2,
    output wire [7:0] dout1,
    output wire [7:0] dout2
    );

   parameter
		ACCESO_M1 = 1,
		READ_M1   = 2,
		WRITE_M1  = 3,
		ACCESO_M2 = 4,
		READ_M2   = 5,
		WRITE_M2  = 6;		

   reg [7:0] data_to_write;
	reg enable_input_to_sram;
	reg write_in_dout1;
	reg write_in_dout2;

	reg [7:0] doutput1;
	reg [7:0] doutput2;

	reg [2:0] state = ACCESO_M1;
	reg [2:0] next_state;
	
	always @(posedge clk) begin
		state <= next_state;
	end

	always @* begin
		next_state = ACCESO_M1;
		data_to_write = 8'h00;
		write_in_dout1 = 0;
		write_in_dout2 = 0;

		case (state)
			ACCESO_M1: begin
					 		 if (we1_n == 1) begin								
								 next_state = READ_M1;
							 end
							 else begin
								 next_state = WRITE_M1;
							 end
						 end
			READ_M1:   begin
			             if (we1_n == 1) begin
                        write_in_dout1 = 1;
                      end
							 next_state = ACCESO_M2;
						 end
			WRITE_M1:  begin
                      if (we1_n == 0) begin
                        enable_input_to_sram = 1;
                        data_to_write = din1;
                        next_state = ACCESO_M2;
                      end
						 end
			ACCESO_M2: begin
							 if (we2_n == 1) begin
							    next_state = READ_M2;
							 end
							 else begin
								 next_state = WRITE_M2;
							 end
						 end
			READ_M2:   begin
                      if (we2_n == 1) begin
                        write_in_dout2 = 1;
                      end
                      next_state = ACCESO_M1;
						 end
			WRITE_M2:  begin
                      if (we2_n == 0) begin
                        enable_input_to_sram = 1;
                        data_to_write = din2;
                        next_state = ACCESO_M1;
                      end
						 end
       endcase
	 end

	// assign doutput1 = oe1_n ? 8'hZZ : doutput1;
	// assign doutput2 = oe2_n ? 8'hZZ : doutput2;
	assign dout1 = doutput1;
	assign dout2 = doutput2;
	 
	 always @(posedge clk) begin
		if (write_in_dout1)
			doutput1 <= data_to_write;
		if (write_in_dout2)
			doutput2 <= data_to_write;
	 end

endmodule