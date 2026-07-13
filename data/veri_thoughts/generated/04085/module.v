
module top_module (
    input [2:0] in,
    output reg [7:0] O
);

    wire [7:0] priority_out;
    wire [3:0] binary_out;
    wire [7:0] final_out;

    priority_encoder pe(in, priority_out);
    binary_to_one_hot btoh(priority_out[3:0], binary_out);
    final_output fo(priority_out, binary_out, final_out);

    always @(*) begin
        O = final_out;
    end

endmodule
module priority_encoder (
    input [2:0] in,
    output reg [7:0] out
);

    always @(*) begin
        case(in)
            3'b000: out = 8'b00000001;
            3'b001: out = 8'b00000010;
            3'b010: out = 8'b00000100;
            3'b011: out = 8'b00001000;
            3'b100: out = 8'b00010000;
            3'b101: out = 8'b00100000;
            3'b110: out = 8'b01000000;
            3'b111: out = 8'b10000000;
        endcase
    end

endmodule
module binary_to_one_hot (
    input [3:0] B,
    output reg [3:0] O
);

    always @(*) begin
        case(B)
            4'b0000: O = 4'b1000;
            4'b0001: O = 4'b0100;
            4'b0010: O = 4'b0010;
            4'b0011: O = 4'b0001;
            default: O = 4'b0000;
        endcase
    end

endmodule
module final_output (
    input [7:0] priority_input,
    input [3:0] one_hot_input,
    output reg [7:0] output_val
);

    always @(*) begin
        case(one_hot_input)
            4'b1000: output_val = priority_input[7:0];
            4'b0100: output_val = priority_input[6:0];
            4'b0010: output_val = priority_input[5:0];
            4'b0001: output_val = priority_input[4:0];
            default: output_val = 8'b0;
        endcase
    end

endmodule