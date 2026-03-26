module mux6 #(parameter WIREWIDTH = 1) (
    input wire [2:0] s,
    input wire [WIREWIDTH-1:0] d0, d1, d2, d3, d4, d5,
    output reg [WIREWIDTH-1:0] o
);
    always @* begin
        case(s)
            3'b000: o = d0;
            3'b001: o = d1;
            3'b010: o = d2;
            3'b011: o = d3;
            3'b100: o = d4;
            default: o = d5;
        endcase
    end

endmodule