module top_module (
    input clk,
    input reset,   // Synchronous active-high reset
    output [3:1] ena,
    output [15:0] q);
    
    wire [3:0] bcd_out;
    wire [15:0] binary_out;
    wire [3:1] ena_out;
    
    binary_to_bcd_converter bcd_converter(
        .binary_in(binary_out),
        .bcd_out(bcd_out)
    );
    
    priority_encoder priority_encoder_inst(
        .in(ena_out),
        .out(ena)
    );
    
    reg [15:0] count;
    reg [3:1] ena_reg;
    
    always @(posedge clk) begin
        if (reset) begin
            count <= 0;
            ena_reg <= 0;
        end
        else begin
            count <= count + 1;
            ena_reg <= ena_out;
        end
    end
    
    assign binary_out = count;
    assign ena_out = {3{1'b1}};
    
    assign q = {bcd_out[3], bcd_out[2], bcd_out[1], bcd_out[0], 12'b0};
    
endmodule

module binary_to_bcd_converter (
    input [15:0] binary_in,
    output [3:0] bcd_out
);
    
    reg [3:0] bcd_reg;
    
    always @* begin
        case (binary_in)
            0: bcd_reg = 4'b0000;
            1: bcd_reg = 4'b0001;
            2: bcd_reg = 4'b0010;
            3: bcd_reg = 4'b0011;
            4: bcd_reg = 4'b0100;
            5: bcd_reg = 4'b0101;
            6: bcd_reg = 4'b0110;
            7: bcd_reg = 4'b0111;
            8: bcd_reg = 4'b1000;
            9: bcd_reg = 4'b1001;
            10: bcd_reg = 4'b0001;
            11: bcd_reg = 4'b0010;
            12: bcd_reg = 4'b0011;
            13: bcd_reg = 4'b0100;
            14: bcd_reg = 4'b0101;
            15: bcd_reg = 4'b0110;
            16: bcd_reg = 4'b0111;
            17: bcd_reg = 4'b1000;
            18: bcd_reg = 4'b1001;
            19: bcd_reg = 4'b0001;
            20: bcd_reg = 4'b0010;
            21: bcd_reg = 4'b0011;
            22: bcd_reg = 4'b0100;
            23: bcd_reg = 4'b0101;
            24: bcd_reg = 4'b0110;
            25: bcd_reg = 4'b0111;
            26: bcd_reg = 4'b1000;
            27: bcd_reg = 4'b1001;
            28: bcd_reg = 4'b0001;
            29: bcd_reg = 4'b0010;
            30: bcd_reg = 4'b0011;
            31: bcd_reg = 4'b0100;
            32: bcd_reg = 4'b0101;
            33: bcd_reg = 4'b0110;
            34: bcd_reg = 4'b0111;
            35: bcd_reg = 4'b1000;
            default: bcd_reg = 4'b0000;
        endcase
    end
    
    assign bcd_out = bcd_reg;
    
endmodule

module priority_encoder (
    input [2:0] in,
    output [2:0] out
);
    
    assign out = ~{in[2], in[1], in[0]};
    
endmodule