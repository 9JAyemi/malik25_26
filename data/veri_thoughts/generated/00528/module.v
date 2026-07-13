module mux2x4(data0, data1, data2, data3, selectInput, out);

    output reg [1:0] out;
    input [1:0] data0, data1, data2, data3;
    input [1:0] selectInput;
    
    always @* begin
        case (selectInput)
            2'b00: out = data0;
            2'b01: out = data1;
            2'b10: out = data2;
            2'b11: out = data3;
            default: out = 2'b00;
        endcase
    end
    
endmodule