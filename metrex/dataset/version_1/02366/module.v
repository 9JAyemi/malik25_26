
module VerificadorSentidoMovimiento(
		_clk_,
		FSM_ready_in,
		piso_actual, 
		solicitud_ps,
		solicitud_p1,
		solicitud_p2,
		solicitud_p3,
		solicitud_p4,
		accion
		);
		
		input [2:0] piso_actual;
		input [1:0] solicitud_ps, solicitud_p1, solicitud_p2, solicitud_p3, solicitud_p4;
		input _clk_, FSM_ready_in;
		output reg [1:0] accion;
		
		always @(posedge _clk_)
			begin
				//acciones para el sotano
				if (piso_actual == 3'b000)
					begin
						if (solicitud_ps == 2'bx1) //No realiza accion
							accion <= 2'b00;
						if (solicitud_ps == 2'bx0)
							begin
							accion <= 2'b10;
							accion <= 2'b01;
							end
						if (solicitud_p1 == 2'bx0 | solicitud_p2 == 2'bx0 | solicitud_p3 == 2'bx0 | solicitud_p4 == 2'bx0)
							accion <= 2'b10;
					end
					
				//acciones para el piso1
				else if (piso_actual == 3'b001)
					begin
						if (solicitud_p1 == 2'bxx)
							accion <= 2'b01;
						if (solicitud_ps == 2'bx1)
							begin
							accion <= 2'b11;
							accion <= 2'b01;
							end
						if (solicitud_p2 == 2'b1x)
							begin
							accion <= 2'b10;
							accion <= 2'b01;
							end
						if (solicitud_p3 == 2'b1x | solicitud_p4 == 2'b1x)
							accion <= 2'b10;
						else if (solicitud_p3 == 2'bx1 | solicitud_p4 == 2'bx1)
							accion <= 2'b11;
						if (solicitud_ps == 2'b0x)
							begin
							accion <= 2'b11;
							accion <= 2'b10;
							end
					end
					
				//acciones para el piso2
				else if (piso_actual == 3'b010)
					begin
						if (solicitud_p2 == 2'bxx)
							accion <= 2'b01;
						if (solicitud_p1 == 2'bx1)
							begin
							accion <= 2'b11;
							accion <= 2'b01;
							end
						if (solicitud_p3 == 2'b1x)
							begin
							accion <= 2'b10;
							accion <= 2'b01;
							end
						if (solicitud_ps == 2'b1x | solicitud_p3 == 2'b1x)
							accion <= 2'b10;
						else if (solicitud_ps == 2'bx1 | solicitud_p3 == 2'bx1)
							accion <= 2'b11;
						if (solicitud_ps == 2'b0x | solicitud_p1 == 2'b0x)
							begin
							accion <= 2'b11;
							accion <= 2'b10;
							end
					end
				
				//acciones para el piso3
				else if (piso_actual == 3'b011)
					begin
						if (solicitud_p3 == 2'bxx)
							accion <= 2'b01;
						if (solicitud_p2 == 2'bx1)
							begin
							accion <= 2'b11;
							accion <= 2'b01;
							end
						if (solicitud_p4 == 2'b1x)
							begin
							accion <= 2'b10;
							accion <= 2'b01;
							end
						if (solicitud_ps == 2'b1x | solicitud_p1 == 2'b1x)
							accion <= 2'b10;
						else if (solicitud_ps == 2'bx1 | solicitud_p1 == 2'bx1)
							accion <= 2'b11;
						if (solicitud_ps == 2'b0x | solicitud_p1 == 2'b0x | solicitud_p2 == 2'b0x)
							begin
							accion <= 2'b11;
							accion <= 2'b10;
							end
					end
				
				//acciones para el piso 4
				else if (piso_actual == 3'b100)
					begin
						if (solicitud_p4 == 2'b1x) //No realiza accion
							accion <= 2'b00;
						if (solicitud_p4 == 2'b0x)
							begin
							accion <= 2'b11;
							accion <= 2'b01;
							end
						if (solicitud_ps == 2'b0x | solicitud_p1 == 2'b0x | solicitud_p2 == 2'b0x | solicitud_p3 == 2'b0x)
							begin
							accion <= 2'b11;
							accion <= 2'b10;
							end
					end
			end
	 
	 
	 
	 
endmodule
