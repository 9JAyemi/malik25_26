module top_module (
    input wire [15:0] in,
    output reg [10:0] out
);

    // Combinational circuit to split input into two 8-bit outputs
    wire [7:0] upper_byte = ~in[15:8];
    wire [7:0] lower_byte = ~in[7:0];

    // Priority encoder to encode 8-bit binary number
    wire [2:0] priority_encoder_output;
    priority_encoder priority_encoder_inst (
        .in(upper_byte),
        .out(priority_encoder_output)
    );

    // Combine outputs from both modules
    always @(*) begin
        out[2:0] = priority_encoder_output;
        out[10:3] = {7'b0, upper_byte} + {3'b0, lower_byte};
    end

endmodule

// Priority encoder module
module priority_encoder (
    input wire [7:0] in,
    output reg [2:0] out
);
    always @(*) begin
        casez(in)
            8'b00000001: out = 0;
            8'b00000010: out = 1;
            8'b00000100: out = 2;
            8'b00001000: out = 3;
            8'b00010000: out = 4;
            8'b00100000: out = 5;
            8'b01000000: out = 6;
            8'b10000000: out = 7;
            default: out = 3'b111; // If no bits are set, output 111
        endcase
    end
endmodule