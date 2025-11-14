
module ascii (
    input clk,
    input scan_ready,
    input [7:0] scan_code,
    output [7:0] ascii
);

    reg [7:0] r_ascii;
    reg [1:0] scan_ready_edge_detect = 2'b00;
    assign ascii = r_ascii;
    
    reg extended = 0;
    reg shift = 0;
    reg [1:0] caps = 2'b00;
    wire caps_lock;
    
    reg [7:0] code;



    reg [7:0] key_code [2:0];
    reg [1:0] key_mem_index = 2'b00;
    reg [1:0] key_current_index = 2'b00;
    reg key_clear = 0;
    
    reg [7:0] current_code;
    reg [7:0] break_code;
    reg [7:0] state_code;
    reg [2:0] state_reg = 2'b00;
    
    parameter st_idle     = 3'b000;
    parameter st_code_1   = 3'b001;
    parameter st_code_2   = 3'b010;
    parameter st_code_3   = 3'b011;
    parameter st_break    = 3'b100;
    parameter st_extended = 3'b101;
    parameter st_ready    = 3'b110;

    

    assign caps_lock = caps[0]; always @(posedge clk) begin
        scan_ready_edge_detect <= {scan_ready_edge_detect[0], scan_ready};
    end      
    

    always @(posedge clk) begin
        case (state_reg) 
            st_idle:
                begin
                    if (scan_ready_edge_detect == 2'b01) begin
                       current_code <= scan_code;
                       state_reg <= st_code_1;
                    end 
                end
            st_code_1:
                begin
                    state_code <= current_code;
                    state_reg <= st_code_2;
                end
            st_code_2:
                begin
                    if (state_code == 8'hf0) begin
                        state_reg <= st_break;
                    end else begin
                        state_reg <= st_code_3;
                    end
                end
            st_code_3:
                begin
                    state_reg <= st_ready;
                end
            st_break:
                begin
                    code <= 8'h00;
                    if (scan_ready_edge_detect == 2'b01) begin
                       state_reg <= st_idle;
                       break_code <= scan_code;
                    end 
                end
            st_extended:
                begin
                
                end
            st_ready:
                begin
                    code <= state_code;
                    state_reg <= st_idle;
                end
            default:
                begin
                
                end
        endcase
        
    end
    
    always @(posedge clk) begin
        if (scan_ready_edge_detect == 2'b01 && code == 8'h58) begin
            caps <= caps + 2'b1;
        end
    end
    
    always @(posedge clk) begin
        if (code == 8'h12 || code == 8'h59) begin
            shift <= 1;
        end else if (break_code == 8'h12 || break_code == 8'h59) begin
            shift <= 0;
        end
    end


    always @(posedge clk) begin

        if (extended) begin
            case (code)
            
                8'h6b: r_ascii <= 8'd130; 8'h75: r_ascii <= 8'd131; 8'h74: r_ascii <= 8'd132; 8'h72: r_ascii <= 8'd133; 8'h6c: r_ascii <= 8'd134; 8'h69: r_ascii <= 8'd135; 8'h7d: r_ascii <= 8'd136; 8'h7a: r_ascii <= 8'd137; 8'h70: r_ascii <= 8'd138; 8'h71: r_ascii <= 8'd139; default: r_ascii <= 8'd0; endcase
        end else
        if ((shift && !caps_lock) || (caps_lock && !shift)) begin     
            case (code)
            
                8'h29: r_ascii <= 8'd32; 8'h16: r_ascii <= 8'd33; 8'h52: r_ascii <= 8'd34; 8'h26: r_ascii <= 8'd35; 8'h25: r_ascii <= 8'd36; 8'h2e: r_ascii <= 8'd37; 8'h3d: r_ascii <= 8'd38; 8'h46: r_ascii <= 8'd40; 8'h45: r_ascii <= 8'd41; 8'h3e: r_ascii <= 8'd42; 8'h55: r_ascii <= 8'd43; 8'h4c: r_ascii <= 8'd58; 8'h41: r_ascii <= 8'd60; 8'h49: r_ascii <= 8'd62; 8'h4a: r_ascii <= 8'd63; 8'h1e: r_ascii <= 8'd64; 8'h1c: r_ascii <= 8'd65; 8'h32: r_ascii <= 8'd66; 8'h21: r_ascii <= 8'd67; 8'h23: r_ascii <= 8'd68; 8'h24: r_ascii <= 8'd69; 8'h2b: r_ascii <= 8'd70; 8'h34: r_ascii <= 8'd71; 8'h33: r_ascii <= 8'd72; 8'h43: r_ascii <= 8'd73; 8'h3b: r_ascii <= 8'd74; 8'h42: r_ascii <= 8'd75; 8'h4b: r_ascii <= 8'd76; 8'h3a: r_ascii <= 8'd77; 8'h31: r_ascii <= 8'd78; 8'h44: r_ascii <= 8'd79; 8'h4d: r_ascii <= 8'd80; 8'h15: r_ascii <= 8'd81; 8'h2d: r_ascii <= 8'd82; 8'h1b: r_ascii <= 8'd83; 8'h2c: r_ascii <= 8'd84; 8'h3c: r_ascii <= 8'd85; 8'h2a: r_ascii <= 8'd86; 8'h1d: r_ascii <= 8'd87; 8'h22: r_ascii <= 8'd88; 8'h35: r_ascii <= 8'd89; 8'h1a: r_ascii <= 8'd90; 8'h36: r_ascii <= 8'd94; 8'h4e: r_ascii <= 8'd95; 8'h54: r_ascii <= 8'd123; 8'h5d: r_ascii <= 8'd124; 8'h5b: r_ascii <= 8'd125; 8'h0e: r_ascii <= 8'd126; default: r_ascii <= 8'd0; endcase
        end else begin
            case (code)
                8'h0d: r_ascii <= 8'd9;  8'h29: r_ascii <= 8'd32;  8'h52: r_ascii <= 8'd39;  8'h7c: r_ascii <= 8'd42;  8'h79: r_ascii <= 8'd43;  8'h41: r_ascii <= 8'd44;  8'h49: r_ascii <= 8'd46;  8'h71: r_ascii <= 8'd46;  8'h4e: r_ascii <= 8'd45;  8'h7b: r_ascii <= 8'd45;  8'h4a: r_ascii <= 8'd47;  8'h45: r_ascii <= 8'd48;  8'h70: r_ascii <= 8'd48;  8'h16: r_ascii <= 8'd49;  8'h69: r_ascii <= 8'd49;  8'h1e: r_ascii <= 8'd50;  8'h72: r_ascii <= 8'd50;  8'h26: r_ascii <= 8'd51;  8'h7a: r_ascii <= 8'd51;  8'h25: r_ascii <= 8'd52;  8'h6b: r_ascii <= 8'd52;  8'h2e: r_ascii <= 8'd53;  8'h73: r_ascii <= 8'd53;  8'h36: r_ascii <= 8'd54;  8'h74: r_ascii <= 8'd54;  8'h3d: r_ascii <= 8'd55;  8'h6c: r_ascii <= 8'd55;  8'h3e: r_ascii <= 8'd56;  8'h75: r_ascii <= 8'd56;  8'h46: r_ascii <= 8'd57;  8'h7d: r_ascii <= 8'd57;  8'h4c: r_ascii <= 8'd59;  8'h55: r_ascii <= 8'd61;  8'h54: r_ascii <= 8'd91;  8'h5d: r_ascii <= 8'd92;  8'h5b: r_ascii <= 8'd93;  8'h0e: r_ascii <= 8'd96;  8'h1c: r_ascii <= 8'd97;  8'h32: r_ascii <= 8'd98;  8'h21: r_ascii <= 8'd99;  8'h23: r_ascii <= 8'd100; 8'h24: r_ascii <= 8'd101; 8'h2b: r_ascii <= 8'd102; 8'h34: r_ascii <= 8'd103; 8'h33: r_ascii <= 8'd104; 8'h43: r_ascii <= 8'd105; 8'h3b: r_ascii <= 8'd106; 8'h42: r_ascii <= 8'd107; 8'h4b: r_ascii <= 8'd108; 8'h3a: r_ascii <= 8'd109; 8'h31: r_ascii <= 8'd110; 8'h44: r_ascii <= 8'd111; 8'h4d: r_ascii <= 8'd112; 8'h15: r_ascii <= 8'd113; 8'h2d: r_ascii <= 8'd114; 8'h1b: r_ascii <= 8'd115; 8'h2c: r_ascii <= 8'd116; 8'h3c: r_ascii <= 8'd117; 8'h2a: r_ascii <= 8'd118; 8'h1d: r_ascii <= 8'd119; 8'h22: r_ascii <= 8'd120; 8'h35: r_ascii <= 8'd121; 8'h1a: r_ascii <= 8'd122; 8'h5a: r_ascii <= 8'd128;  8'h66: r_ascii <= 8'd129;  8'h76: r_ascii <= 8'd140;  8'h05: r_ascii <= 8'd141;  8'h06: r_ascii <= 8'd142;  8'h04: r_ascii <= 8'd143;  8'h0c: r_ascii <= 8'd144;  8'h03: r_ascii <= 8'd145;  8'h0b: r_ascii <= 8'd146;  8'h83: r_ascii <= 8'd147;  8'h0a: r_ascii <= 8'd148;  8'h01: r_ascii <= 8'd149;  8'h09: r_ascii <= 8'd150;  8'h78: r_ascii <= 8'd151;  8'h07: r_ascii <= 8'd152;  default: r_ascii <= 8'd0; endcase
        end
        
    end
    
endmodule
