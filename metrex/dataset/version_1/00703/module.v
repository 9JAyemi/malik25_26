module keyboard_pressed_status (
    input wire clk,
    input wire rst,
    input wire scan_received,
    input wire [7:0] scancode,
    input wire extended,
    input wire released,
    output reg kbclean
    );
    
    parameter
        RESETTING = 2'd0,
        UPDATING  = 2'd1,
        SCANNING  = 2'd2;
        
    reg keybstat_ne[0:255];  // non extended keymap
    reg keybstat_ex[0:255];  // extended keymap
    reg [7:0] addrscan = 8'h00; // keymap bit address
    reg keypressed_ne = 1'b0; // there is at least one key pressed
    reg keypressed_ex = 1'b0; // there is at least one extended key pressed
    reg [1:0] state = RESETTING;
    
    integer i;
    initial begin
        kbclean = 1'b1;
        for (i=0;i<256;i=i+1) begin
            keybstat_ne[i] = 1'b0;
            keybstat_ex[i] = 1'b0;
        end
    end
    
    always @(posedge clk) begin
        if (rst == 1'b1) begin
            state <= RESETTING;
            addrscan <= 8'h00;
        end
        else begin
            case (state)
                RESETTING:
                    begin
                        if (addrscan == 8'hFF) begin
                            addrscan <= 8'h00;
                            state <= SCANNING;
                            kbclean <= 1'b1;
                        end
                        else begin
                            keybstat_ne[addrscan] <= 1'b0;
                            keybstat_ex[addrscan] <= 1'b0;
                            addrscan <= addrscan + 8'd1;
                        end
                    end
                UPDATING:
                    begin
                        state <= SCANNING;
                        addrscan <= 8'h00;
                        kbclean <= 1'b0;
                        keypressed_ne <= 1'b0;
                        keypressed_ex <= 1'b0;
                        if (extended == 1'b0)
                            keybstat_ne[scancode] <= ~released;
                        else
                            keybstat_ex[scancode] <= ~released;
                    end
                SCANNING:
                    begin
                        if (scan_received == 1'b1)
                            state <= UPDATING;
                        addrscan <= addrscan + 8'd1;
                        if (addrscan == 8'hFF) begin
                            kbclean <= ~(keypressed_ne | keypressed_ex);
                            keypressed_ne <= 1'b0;
                            keypressed_ex <= 1'b0;
                        end
                        else begin
                            keypressed_ne <= keypressed_ne | keybstat_ne[addrscan];
                            keypressed_ex <= keypressed_ex | keybstat_ex[addrscan];
                        end
                    end
            endcase
        end
    end
endmodule