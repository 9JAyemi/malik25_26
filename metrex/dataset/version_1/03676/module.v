
module seven_seg (
                    clk,
                    clr,
                    disp_num,   
                    Scanning,   
                    SW,
                    AN,     
                    SEGMENT     
                    );

    input wire          clk, clr;
    input wire  [ 1: 0] Scanning;       
    input wire  [ 1: 0] SW;
    input wire  [31: 0] disp_num;       
    
    output reg  [ 3: 0] AN;             
    output wire [ 7: 0] SEGMENT;     

    reg         [ 3: 0] digit       = 4'h0;
    reg         [ 7: 0] temp_seg    = 8'h0, 
                        digit_seg   = 8'h0;
    wire        [15: 0] disp_current;

    assign SEGMENT = SW[0] ? digit_seg : temp_seg;                  assign disp_current = SW[1] ? disp_num[31:16] : disp_num[15:0]; always @(posedge clk)begin
        case (digit)
            4'h0:     digit_seg = 8'b10000001; 
		    4'h1:     digit_seg = 8'b11001111; 
		    4'h2:     digit_seg = 8'b10010010; 
		    4'h3:     digit_seg = 8'b10000110; 
		    4'h4:     digit_seg = 8'b11001100; 
		    4'h5:     digit_seg = 8'b10100100; 
		    4'h6:     digit_seg = 8'b10100000; 
		    4'h7:     digit_seg = 8'b10001111; 
		    4'h8:     digit_seg = 8'b10000000; 
		    4'h9:     digit_seg = 8'b10000100; 
		    4'hA:     digit_seg = 8'b10001000; 
		    4'hB:     digit_seg = 8'b11100000; 
		    4'hC:     digit_seg = 8'b10110001; 
		    4'hD:     digit_seg = 8'b11000010; 
		    4'hE:     digit_seg = 8'b10110000; 
		    4'hF:     digit_seg = 8'b10111000;
            default:  digit_seg = 8'b00000000;
    endcase
   end
    
    always @(posedge clk)begin
        case (Scanning)             0: begin digit       = disp_current[ 3: 0]; temp_seg    = { disp_num[24], disp_num[ 0], disp_num[ 4], disp_num[16],
                                    disp_num[25], disp_num[17], disp_num[ 5], disp_num[12]};
                    AN          = 4'b1110;
                end
                1: begin digit       = disp_current[ 7: 4]; temp_seg    = { disp_num[26], disp_num[ 1], disp_num[ 6], disp_num[18],
									disp_num[27], disp_num[19], disp_num[ 7], disp_num[13]};
                    AN          = 4'b1101;
                end
                2: begin digit       = disp_current[11: 8];   temp_seg    = { disp_num[28], disp_num[ 2], disp_num[ 8], disp_num[20],
									disp_num[29], disp_num[21], disp_num[ 9], disp_num[14]};
                    AN          = 4'b1011;
                end
                3: begin digit       = disp_current[15:12];  temp_seg    = { disp_num[30], disp_num[ 3], disp_num[10], disp_num[22],
									disp_num[31], disp_num[23], disp_num[11], disp_num[15]};
                    AN          = 4'b0111;
               end
     endcase
    end  
    

 
endmodule
