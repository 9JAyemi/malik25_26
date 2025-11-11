
module shift_mux_xor (
    input clk,
    input [255:0] in, // 256-bit input for the shift register
    output [7:0] q // 8-bit output from the XOR gate
);

    // Define the 256-bit shift register
    reg [255:0] shift_reg;
    always @(posedge clk) begin
        shift_reg <= {shift_reg[254:0], in[0]};
    end

    // Define the 8-to-1 multiplexer
    reg [7:0] mux_inputs [7:0];
    always @(*) begin
        mux_inputs[0] = 8'h01;
        mux_inputs[1] = 8'h02;
        mux_inputs[2] = 8'h04;
        mux_inputs[3] = 8'h08;
        mux_inputs[4] = 8'h10;
        mux_inputs[5] = 8'h20;
        mux_inputs[6] = 8'h40;
        mux_inputs[7] = 8'h80;
    end
    reg [2:0] counter;
    always @(posedge clk) begin
        counter <= counter + 1;
    end
    wire [7:0] mux_output;
    assign mux_output = mux_inputs[counter];

    // Define the XOR gate
    wire [255:0] xor_input;
    assign xor_input = {shift_reg[255], shift_reg[127], shift_reg[63], shift_reg[31], shift_reg[15], shift_reg[7], shift_reg[3], shift_reg[1]};
    assign q = xor_input[7] ^ xor_input[6] ^ xor_input[5] ^ xor_input[4] ^ xor_input[3] ^ xor_input[2] ^ xor_input[1] ^ xor_input[0];

endmodule
module top_module (
    input clk,
    input [255:0] in, // 256-bit input for the shift register
    output [7:0] q // 8-bit output from the XOR gate
);

    shift_mux_xor smx (.clk(clk), .in(in), .q(q));

endmodule