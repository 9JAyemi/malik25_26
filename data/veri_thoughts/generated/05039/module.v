module Span12Mux_s2_h(
    input [11:0] I,
    input [1:0] S,
    output reg [11:0] O
);

always @(*) begin
    case (S)
        2'b00: O = I;
        2'b01: O = {I[11:0]};
        2'b10: O = {I[5:0], I[11:6]};
        2'b11: O = {I[11:6], I[5:0]}; // fixed part select order
        default: O = 12'hXXXX; // handle invalid select signals
    endcase;
end
endmodule