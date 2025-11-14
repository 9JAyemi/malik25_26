module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [7:0] d,    // 8-bit input for the shift register
    output [7:0] q    // 8-bit output from the shift register
);
    
    wire [3:0] johnson_out;
    wire [7:0] xor_out;
    
    johnson_counter jc(
        .clk(clk),
        .reset(reset),
        .q(johnson_out)
    );
    
    xor_module xm(
        .in1(q),
        .in2(johnson_out),
        .out(xor_out)
    );
    
    reg [7:0] shift_reg;
    
    always @(posedge clk) begin
        if (reset) begin
            shift_reg <= 8'h34;
        end else begin
            shift_reg <= {shift_reg[6:0], d};
        end
    end
    
    assign q = xor_out;
    
endmodule

module johnson_counter (
    input clk, 
    input reset,      // Asynchronous active-low reset
    output reg [3:0] q // 4-bit Johnson counter output
);
    
    always @(posedge clk or negedge reset) begin
        if (!reset) begin
            q <= 4'b0000;
        end else begin
            case (q)
                4'b0000: q <= 4'b1000;
                4'b1000: q <= 4'b1100;
                4'b1100: q <= 4'b1110;
                4'b1110: q <= 4'b1111;
                4'b1111: q <= 4'b0111;
                4'b0111: q <= 4'b0011;
                4'b0011: q <= 4'b0001;
                4'b0001: q <= 4'b0000;
            endcase
        end
    end
    
endmodule

module xor_module (
    input [7:0] in1,  // 8-bit input from shift register
    input [3:0] in2,  // 4-bit input from Johnson counter
    output reg [7:0] out // 8-bit output after XOR operation
);
    
    always @(*) begin
        case (in2)
            4'b0000: out = in1 ^ 8'h00;
            4'b1000: out = in1 ^ 8'h08;
            4'b1100: out = in1 ^ 8'h0C;
            4'b1110: out = in1 ^ 8'h0E;
            4'b1111: out = in1 ^ 8'h0F;
            4'b0111: out = in1 ^ 8'h07;
            4'b0011: out = in1 ^ 8'h03;
            4'b0001: out = in1 ^ 8'h01;
        endcase
    end
    
endmodule