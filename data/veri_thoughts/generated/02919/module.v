module ram_RAMB18E1 #(parameter LOC = "RAMB18_X0Y0", parameter WRITE_MODE_A = "WRITE_FIRST")
(
    input wire clk,
    input wire [7:0] din,
    output wire [7:0] dout
);

reg [7:0] mem [0:31];

integer i;

initial begin
    for (i = 0; i < 32; i = i + 1) begin
        mem[i] = 8'h00;
    end
end

always @(posedge clk) begin
    if (WRITE_MODE_A == "WRITE_FIRST") begin
        mem[0] <= {din, mem[0][7:1]};
    end
end

assign dout = mem[0];

endmodule