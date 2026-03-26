module barrel_shifter_register (
    input wire [15:0] in,
    input wire clk,
    input wire reset,
    output wire [7:0] q
);

reg [7:0] register;

always @(posedge clk) begin
    if (reset) begin
        register <= 8'b0;
    end else begin
        register <= in[15:8];
    end
end

assign q = register;

endmodule

module top_module (
    input wire [15:0] in,
    input wire clk,
    input wire reset,
    output wire [7:0] q
);

wire [7:0] register_output;

barrel_shifter_register barrel_shifter_register_inst (
    .in(in),
    .clk(clk),
    .reset(reset),
    .q(register_output)
);

assign q = register_output;

endmodule