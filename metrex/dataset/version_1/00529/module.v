module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [2:0] sel,  // Select input to choose between multiplexer and logical operations modes
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output reg [3:0] out,   // Output data
    output reg out_and,     // Output of NAND gate for logical operations
    output reg out_or,      // Output of NAND gate for logical operations
    output reg out_xor      // Output of NAND gate for logical operations
);

reg [3:0] mux_out;
reg [3:0] nand_in;
reg [3:0] nand_in_neg;
reg [3:0] nand_out;

always @(posedge clk, posedge reset) begin
    if (reset) begin
        out <= 4'b0;
        out_and <= 1'b0;
        out_or <= 1'b0;
        out_xor <= 1'b0;
    end else begin
        case (sel)
            3'b000: begin
                mux_out <= data0;
            end
            3'b001: begin
                mux_out <= data1;
            end
            3'b010: begin
                mux_out <= data2;
            end
            3'b011: begin
                mux_out <= data3;
            end
            3'b100: begin
                mux_out <= data4;
            end
            3'b101: begin
                mux_out <= data5;
            end
            default: begin
                mux_out <= mux_out;
            end
        endcase
        
        nand_in[0] <= mux_out[0];
        nand_in[1] <= mux_out[1];
        nand_in[2] <= mux_out[2];
        nand_in[3] <= mux_out[3];
        
        nand_in_neg[0] <= ~mux_out[0];
        nand_in_neg[1] <= ~mux_out[1];
        nand_in_neg[2] <= ~mux_out[2];
        nand_in_neg[3] <= ~mux_out[3];
        
        nand_out[0] <= ~(nand_in[0] & nand_in[1] & nand_in[2] & nand_in[3]);
        nand_out[1] <= ~(nand_in_neg[0] & nand_in_neg[1] & nand_in_neg[2] & nand_in_neg[3]);
        nand_out[2] <= ~(nand_in[0] & nand_in_neg[1] & nand_in_neg[2] & nand_in[3] | nand_in_neg[0] & nand_in[1] & nand_in[2] & nand_in_neg[3]);
        
        out <= mux_out;
        out_and <= nand_out[0];
        out_or <= nand_out[1];
        out_xor <= nand_out[2];
    end
end

endmodule