module twos_complement (
    input [3:0] a,
    output reg [3:0] twos_comp
);

reg [3:0] ones_comp;
reg [3:0] inverted;
reg [3:0] add_one;

always @ (a) begin
    ones_comp = ~a;
    inverted = ones_comp + 4'b1;
    add_one = inverted[3] ? inverted + 4'b1 : inverted;
    twos_comp <= add_one;
end

endmodule