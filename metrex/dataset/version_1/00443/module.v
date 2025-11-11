
module bmu(input cx0, cx1, output reg [1:0] bm);
    always @(cx0, cx1) begin
        case ({cx1,cx0})
            2'b00: bm=2'b00;
            2'b01: bm=2'b01;
            2'b10: bm=2'b10;
            2'b11: bm=2'b11;
        endcase
    end
endmodule
