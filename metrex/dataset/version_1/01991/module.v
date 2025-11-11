module srl8_to_64(clk, enable, reset, dataIn, ready, result); 
    input clk, enable, reset; 
    input [7:0] dataIn; 
    output ready; 
    output [63:0] result; 

    reg [7:0] regBank[7:0]; 
    reg [3:0] status_int;
    integer i; 

    parameter s1=0, s2=1, s3=2, s4=3, s5=4, s6=5, s7=6, s8=7, s9=8; 

    always @(posedge clk)
    begin
        if (reset == 1)
        begin
            status_int <= s1;
            for (i=0; i<8; i=i+1) begin 
                regBank[i] <= 8'h0; 
            end 
        end else 
        if (enable == 0)
        begin
            regBank[0] <= dataIn; 
            for (i=7; i>0; i=i-1) begin 
                regBank[i] <= regBank[i-1]; 
            end 
            if (status_int == s9) begin
                status_int <= s1;
            end else begin
                status_int <= status_int + 1;
            end
        end else begin
            status_int <= s1;
        end
    end

    assign result = (status_int == s9) ? {regBank[7], regBank[6], regBank[5], regBank[4], regBank[3], regBank[2], regBank[1], regBank[0]} : 64'h0; 
    assign ready = (status_int == s9) ? 1'b1 : 1'b0;
endmodule