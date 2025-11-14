
module top_module (
    input clk,
    input [15:0] in, // 16 inputs for the multiplexer
    input [3:0] sel, // 4-bit select input for the multiplexer
    output q // Output of the final logical operation module
);

    reg [15:0] mux_out; // Output of the multiplexer
    reg d_ff_out; // Output of the dual-edge triggered flip-flop
    reg d_ff_out_r; // Registered version of d_ff_out
    wire [15:0] or_in; // Input to the logical operation module

    // Multiplexer implementation
    always @(*) begin
        case (sel)
            4'b0000: mux_out = in[0];
            4'b0001: mux_out = in[1];
            4'b0010: mux_out = in[2];
            4'b0011: mux_out = in[3];
            4'b0100: mux_out = in[4];
            4'b0101: mux_out = in[5];
            4'b0110: mux_out = in[6];
            4'b0111: mux_out = in[7];
            4'b1000: mux_out = in[8];
            4'b1001: mux_out = in[9];
            4'b1010: mux_out = in[10];
            4'b1011: mux_out = in[11];
            4'b1100: mux_out = in[12];
            4'b1101: mux_out = in[13];
            4'b1110: mux_out = in[14];
            4'b1111: mux_out = in[15];
        endcase
    end

    // Dual-edge triggered flip-flop implementation
    always @(posedge clk) begin
        d_ff_out <= mux_out;
    end

    always @(negedge clk) begin
        d_ff_out_r <= d_ff_out;
    end

    // Logical operation module implementation
    assign or_in = {16{d_ff_out_r}} | in;
    assign q = |or_in;

endmodule