
module FSM_Convert_Fixed_To_Float(
		input wire CLK,           input wire RST_FF,        input wire Bandcomp,      input wire Begin_FSM_FF,  input wire [7:0] Encd,    output reg EN_REG1,       output reg EN_REGmult,    output reg LOAD,          output reg MS_1,          output reg ACK_FF,        output reg EN_MS_1,
        output reg EN_REG2,
        output reg RST

	 );

parameter [3:0] 
    a = 4'b0000,
		b = 4'b0001,
	    c = 4'b0010,
	    d = 4'b0011,
	    e = 4'b0100,
	    f = 4'b0101,
		g = 4'b0110,
		h = 4'b0111,
		i = 4'b1000,
		j = 4'b1001,
		k = 4'b1010;
					
    reg [3:0] state_reg, state_next ; always @(posedge CLK, posedge RST_FF)
	   if (RST_FF)
	      begin
		  state_reg <= a;	
	      end
	   else 
	      begin
		  state_reg <= state_next;
	   end

always @*
    begin
	state_next = state_reg;
	
	EN_REG1 = 1'b0;
	EN_REGmult = 1'b0;
	EN_REG2 = 1'b0;
    ACK_FF = 1'b0;
    EN_MS_1 = 1'b0;
    MS_1 = 1'b0;
    LOAD = 1'b0;
    RST = 1'b0;
    
	case(state_reg)
	    a: 
        begin
                
            if(Begin_FSM_FF) 
                begin
                RST = 1'b1;
                ACK_FF = 1'b0;    
                state_next = b;
                end
            else  
                state_next = a;
           
        end
            
		b: 
		begin
		    EN_REG1 = 1'b1;    
	        state_next = c;
		end
		
		c:
		begin
		    state_next = d;
		end
		
		d: 
        begin
            EN_REGmult = 1'b1;    
            state_next = e;
        end
		
		e:
		begin
			EN_MS_1 = 1'b1;
			if(Encd == 8'b00011010)
                state_next = k;
            else
            state_next = f;
		end
		
		f:
        begin
            EN_MS_1 = 1'b1;
            MS_1 = 1'b1;
            state_next = g;
        end
        
        g:
        begin
            state_next = h;
        end     
           		
		h:
		begin
		    LOAD = 1'b1;
		    state_next = i;
        end
	
	    i:
        begin
            EN_REG2 = 1'b1;
            state_next = j;
        end
            
		j:
		begin			
			ACK_FF = 1'b1;
			if(RST_FF)
                 state_next = a;
            else
                state_next = j;
		end
		
		k:
        begin
            state_next = h;
        end
                
	endcase
    end

endmodule
