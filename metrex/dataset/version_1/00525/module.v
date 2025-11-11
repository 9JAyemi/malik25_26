module RAM(
    input wire clka,
    input wire wea,
    input wire [6:0] addra,
    input wire [31:0] dina,
    output reg [31:0] douta
);

reg [31:0] memory[0:127];

always @(posedge clka) begin
    if(wea) begin
        memory[addra] <= dina;
    end
    douta <= memory[addra];
end

endmodule