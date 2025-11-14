module gray_code_counter (
    input CLK,
    input RST,
    output reg [7:0] count_gray
);

    reg [7:0] count_binary;
    
    always @(posedge CLK or negedge RST) begin
        if (RST == 0) begin
            count_binary <= 8'b00000000;
            count_gray <= 8'b00000000;
        end
        else begin
            count_binary <= count_binary + 1;
            count_gray <= count_binary ^ (count_binary >> 1);
        end
    end
    
endmodule