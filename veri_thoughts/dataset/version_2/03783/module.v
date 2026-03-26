module ring_counter_shift_register_decoder_mux (
    input clk,
    input d,
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);

reg [2:0] shift_reg;
wire [1:0] decoder_out;
wire [7:0] mux_out;

// Ring counter shift register
always @(posedge clk) begin
    shift_reg <= {shift_reg[1:0], d};
end

// Decoder
assign decoder_out = shift_reg[2:1];

// Multiplexer
assign mux_out = (decoder_out == 2'b00) ? in[7:0] :
                 (decoder_out == 2'b01) ? in[15:8] :
                 (decoder_out == 2'b10) ? in[7:0] :
                                         in[15:8];

// Output
assign out_hi = (decoder_out == 2'b01) ? mux_out : 8'b0;
assign out_lo = (decoder_out == 2'b10) ? mux_out : 8'b0;

endmodule