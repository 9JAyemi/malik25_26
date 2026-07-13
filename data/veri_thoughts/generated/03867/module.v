module top_module (
    input clk,
    input reset,
    input enable,
    input select,
    output reg [3:0] out
);

    wire [1:0] decoder_out;
    wire [3:0] counter_out;
    wire [3:0] func_out;
    
    decoder_2to4 decoder(clk, enable, decoder_out);
    counter_4bit counter(clk, reset, decoder_out[0], counter_out);
    functional_module func(clk, reset, select, counter_out, func_out);
    
    always @(posedge clk) begin
        if (reset) begin
            out <= 4'b0000;
        end else begin
            if (decoder_out[1]) begin
                out <= func_out;
            end else begin
                out <= counter_out;
            end
        end
    end

endmodule

module decoder_2to4 (
    input clk,
    input enable,
    output reg [1:0] out
);

    always @(posedge clk) begin
        if (enable) begin
            out <= 2'b00;
        end else begin
            case (out)
                2'b00: out <= 2'b01;
                2'b01: out <= 2'b10;
                2'b10: out <= 2'b11;
                2'b11: out <= 2'b00;
            endcase
        end
    end

endmodule

module counter_4bit (
    input clk,
    input reset,
    input enable,
    output reg [3:0] out
);

    always @(posedge clk) begin
        if (reset) begin
            out <= 4'b0000;
        end else begin
            if (enable) begin
                out <= out + 1;
            end
        end
    end

endmodule

module functional_module (
    input clk,
    input reset,
    input select,
    input [3:0] counter_in,
    output reg [3:0] out
);

    always @(posedge clk) begin
        if (reset) begin
            out <= 4'b0000;
        end else begin
            if (select) begin
                out <= counter_in + select;
            end
        end
    end

endmodule