module mux4to1_enable(
    input wire [3:0] in,
    input wire [1:0] sel,
    input wire ena,
    output reg out
);

// The most significant bit is used as output
wire [3:0] selected_input;
assign selected_input = in[sel];

always @(posedge ena) begin
    if (ena) begin
        out <= selected_input;
    end else begin
        out <= 4'b0;
    end
end

endmodule