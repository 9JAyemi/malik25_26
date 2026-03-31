module twos_complement (
    input [3:0] binary,
    output reg [3:0] twos_comp
);

reg [3:0] invert;
reg [3:0] add_one;

always @* begin
    invert = ~binary;
end

always @* begin
    add_one = invert + 4'b0001;
end

always @* begin
    twos_comp = add_one;
end

endmodule