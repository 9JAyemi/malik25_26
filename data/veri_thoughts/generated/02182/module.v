
module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    output [3:0] counter_out, // 4-bit output from the counter
    input [3:0] encoder_in, // 4-bit input for the priority encoder
    output [1:0] encoder_out, // 2-bit output from the priority encoder
    output [3:0] and_out // 4-bit output from the AND module
);

reg [3:0] counter_reg; // Register to hold the counter value

// Counter module
always @(posedge clk) begin
    if (reset) begin
        counter_reg <= 4'b0000;
    end else begin
        counter_reg <= counter_reg + 1'b1;
    end
end

// Priority encoder module
reg [1:0] encoder_out_reg;
always @(*) begin
    case(encoder_in)
        4'b0001: encoder_out_reg = 2'b00;
        4'b0010: encoder_out_reg = 2'b01;
        4'b0100: encoder_out_reg = 2'b10;
        4'b1000: encoder_out_reg = 2'b11;
        default: encoder_out_reg = 2'b00;
    endcase
end
assign encoder_out = encoder_out_reg;

// AND module
assign and_out = counter_reg & {2'b00, encoder_out};

assign counter_out = counter_reg;

endmodule