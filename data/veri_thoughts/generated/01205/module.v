
module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [2:0] select1,   // Select input for choosing which module's output to use as input 1
    input [2:0] select2,   // Select input for choosing which bit of the decoder's output to use as input 2
    output reg out);   // Output of the functional module

    reg [3:0] counter;
    wire [7:0] decoder_output;
    wire [2:0] decoder_input;
    wire [3:0] counter_output;

    // Instantiate the 4-bit binary counter
    counter counter_inst (
        .clk(clk),
        .reset(reset),
        .out(counter_output)
    );

    // Instantiate the 3-to-8 decoder
    decoder decoder_inst (
        .in(decoder_input),
        .out(decoder_output)
    );

    // Connect the select inputs to the appropriate signals
    assign decoder_input = select2;

    always @(posedge clk) begin
        if (reset) begin
            counter <= 0;
        end else begin
            counter <= counter + 1;
        end
    end

    always @ (*) begin
        case (select1)
            3'b000: out = counter_output[select2] & decoder_output[0];
            3'b001: out = counter_output[select2] & decoder_output[1];
            3'b010: out = counter_output[select2] & decoder_output[2];
            3'b011: out = counter_output[select2] & decoder_output[3];
            3'b100: out = counter_output[select2] & decoder_output[4];
            3'b101: out = counter_output[select2] & decoder_output[5];
            3'b110: out = counter_output[select2] & decoder_output[6];
            3'b111: out = counter_output[select2] & decoder_output[7];
        endcase
    end

endmodule
module counter (
    input clk,
    input reset,
    output reg [3:0] out
);

    always @(posedge clk) begin
        if (reset) begin
            out <= 0;
        end else begin
            out <= out + 1;
        end
    end

endmodule
module decoder (
    input [2:0] in,
    output reg [7:0] out
);

    always @ (*) begin
        case (in)
            3'b000: out = 8'b0000_0001;
            3'b001: out = 8'b0000_0010;
            3'b010: out = 8'b0000_0100;
            3'b011: out = 8'b0000_1000;
            3'b100: out = 8'b0001_0000;
            3'b101: out = 8'b0010_0000;
            3'b110: out = 8'b0100_0000;
            3'b111: out = 8'b1000_0000;
        endcase
    end

endmodule