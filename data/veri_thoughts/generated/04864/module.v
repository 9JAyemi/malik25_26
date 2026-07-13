module message_display_system (
    input clk,
    input reset,   // Synchronous active-high reset
    input [7:0] message,   // ASCII message string input
    output [15:0] display  // 16-character display output
);

    // 4:16 decoder
    wire [15:0] decoder_output;
    decoder_4to16 decoder(
        .in({message[3], message[2], message[1], message[0]}),
        .out(decoder_output)
    );

    // 16-bit shift register
    reg [15:0] shift_register;
    always @(posedge clk) begin
        if (reset) begin
            shift_register <= 16'b0;
        end else begin
            shift_register <= {shift_register[14:0], decoder_output[15]};
        end
    end

    // Output display
    assign display = shift_register;

endmodule

// 4:16 decoder module
module decoder_4to16 (
    input [3:0] in,
    output reg [15:0] out
);

    always @* begin
        case (in)
            4'b0000: out = 16'b0000000000000001;
            4'b0001: out = 16'b0000000000000010;
            4'b0010: out = 16'b0000000000000100;
            4'b0011: out = 16'b0000000000001000;
            4'b0100: out = 16'b0000000000010000;
            4'b0101: out = 16'b0000000000100000;
            4'b0110: out = 16'b0000000001000000;
            4'b0111: out = 16'b0000000010000000;
            4'b1000: out = 16'b0000000100000000;
            4'b1001: out = 16'b0000001000000000;
            4'b1010: out = 16'b0000010000000000;
            4'b1011: out = 16'b0000100000000000;
            4'b1100: out = 16'b0001000000000000;
            4'b1101: out = 16'b0010000000000000;
            4'b1110: out = 16'b0100000000000000;
            4'b1111: out = 16'b1000000000000000;
            default: out = 16'b0000000000000000;
        endcase
    end

endmodule