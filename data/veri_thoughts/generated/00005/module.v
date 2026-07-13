
module resultcounter (resultID, newresult, done, reset, globalreset, clk);

    input[1:0] resultID; 
    input newresult; 
    output[1:0] done; 
    input reset; 
    input globalreset; 
    input clk; 

    reg[3:0] count; 
    reg[1:0] curr; 

    assign done = (count == 0) ? {curr[1], curr[0]} : 2'b00 ;

    always @(posedge clk)
    begin
        if (globalreset)
        begin
            count <= 4'b1000;
            curr <= 2'b00;
        end
        else if (reset || count == 0)
        begin
            count <= 4'b1000;
            curr <= 2'b00;
        end
        else if (newresult && resultID != 2'b00)
        begin
            count <= count - 1;
            curr <= resultID;
        end
    end 
endmodule